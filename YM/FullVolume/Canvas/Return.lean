import YM.FullVolume.Canvas.Reservoir
/- Adapt Curvature loop ColorPipe & Reach -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary
open Shade Function Filter Finset Lattice RG Wilson Exterior Precision Bloch Laurent Tree
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {m : ℕ → Side}
lemma siences (G : Gauge) (hG : G.Simple) (σ : ℝ) (hs : 0<σ) :
    ∃ η K : ℝ, 0<η ∧ η ≤ σ ∧ 0≤K ∧ ∀ (m : ℕ→Side), Tendsto (fun i => (m i).val) atTop atTop →
    ∀ U : ∀ i, Link G (m i)→ℝ, ∀ W T : ∀ i, Link G (m i)→ℝ,
    ∀ (A B M : ℝ) (ε : ℕ → ℝ) (f g : Picture G 1) (R : FaceRow) (i : G.ColorIndex),
      0≤A → 0≤B → 0≤M → Tendsto ε atTop (𝓝 0) → R.strip σ M → R.read 0=1 →
      (∀ i,Pointwise (U i) ∧ Pointwise (W i) ∧ Pointwise (T i)) →
      (∀ i j,Firm σ A (f i j) ∧ Firm σ B (g i j) ∧ Rays 4 (g i j ∘ axes)) →
      (∀ i,Recorded (slots R G) (T i) 0 ∧ Recorded f (U i) (cents (m i)*ε i) ∧ Recorded g (W i) 0) →
    ∃ Q:Skin G 1,
      let a := alphaPay i f
      AtomWall (issue Q) η ((A + |a| * bedCharge σ M+B)*K) ∧ Bs G (issue Q) ∧
      ∀ i, aperture (cents (m i)*ε i) (turnSeries (m:=m i) (issue Q)) (U i-a • T i + W i) 1 := by
  obtain ⟨η,C,hh,hη,hC,H⟩ := veins G σ hs
  refine ⟨η,C*inkCost G 1 η,hh,hη,mul_nonneg hC (inkCost_nonneg ..),fun m hm U W T A B M ε f g R i hA hB hM he hR hg hP hF hu => ?_⟩
  let a := alphaPay i f
  let V := fun i => U i-a • T i
  let p := f-(a:ℂ) • slots R G
  let u := A + |a| * bedCharge σ M
  have hE (i) : Recorded p (V i) (cents (m i)*ε i) :=
    Recorded.less (F:=U i) (H:=a • T i) (hP i).1.analytic (((hP i).2.2.coin a).analytic) (hu i).2.1
      ((hu i).1.weigh a (hP i).2.2.analytic)
  have hT i j : Firm σ u (p i j) := by
    have hh := ((hF i j).1).sub ((Firm.const (α:=Keys 1) hs (a:ℂ)).mul (slots_cost hs hR i j))
    rw [Complex.norm_real, Real.norm_eq_abs] at hh; exact hh
  have hV (i) : Pointwise (V i) := (hP i).1.sub ((hP i).2.2.coin a)
  have h' := point_receipt hG hm (fun i j => (hF i j).1) he (fun i => (hu i).2.1) (fun i => (hP i).1)
  have hp := point_receipt hG hm hT he hE hV
  have hx : leapTip p (step (0:Axis)) 1 ![i,i]=0 := subtract_fee i h' hR hs hg rfl
  have hw k j := hp.vanish hG 1 0 (by decide) i hx k j
  have hF' i j : Firm σ (u+B) ((p+g) i j) := (hT i j).add (hF i j).2.1
  have hz i := Recorded.both (hV i).analytic ((hP i).2.1).analytic (hE i) (hu i).2.2
  have H' := point_receipt hG (F:=V+W) hm hF' he hz (fun i => (hV i).add (hP i).2.1)
  obtain ⟨Q,hQ,hO⟩ := H (u+B) 2 (p+g) (by unfold u; have hp := bedCharge_nonneg (σ:=σ) hM; positivity) H'.toFeatures (fun i j => (hw i j).add (hF i j).2.2)
  obtain ⟨hi,hb⟩ := artery_funded hQ
  refine ⟨Q,⟨by rw [← mul_assoc]; exact hi,hb⟩, fun i x R hv => issue_normal hQ.price hh hO R hv i x,?_⟩
  intro i
  have hh' := (hV i).add (hP i |>.2.1)
  exact colors_align _ hh'.analytic hh'.lights (p+g) Q hQ hh (hz i)

lemma belleron (G : Gauge) (hG : G.Simple) (σ : ℝ) (hs : 0<σ) :
    ∃ (V:Vow G 1), ∃ η K : ℝ, 0<η ∧ η ≤ σ ∧ η < V.δ ∧ 0≤K ∧ ∀ (m : ℕ→Side), Tendsto (fun i => (m i).val) atTop atTop →
    ∀ U : ∀ i, Link G (m i)→ℝ, ∀ W T : ∀ i, Link G (m i)→ℝ,
    ∀ (A B M : ℝ) (ε : ℕ → ℝ) (f g : Picture G 1) (R : FaceRow) (i : G.ColorIndex),
      0≤A → 0≤B → 0≤M → Tendsto ε atTop (𝓝 0) → R.strip σ M → R.read 0=1 →
      (∀ i,Pointwise (U i) ∧ Pointwise (W i) ∧ Pointwise (T i)) →
      (∀ i j,Firm σ A (f i j) ∧ Firm σ B (g i j) ∧ Rays 4 (g i j ∘ axes)) →
      (∀ i,Recorded (slots R G) (T i) 0 ∧ Recorded f (U i) (cents (m i)*ε i) ∧ Recorded g (W i) 0) →
    ∃ Q∈ V.royal m,
      let a := alphaPay i f
      ‖Q‖≤ ((A + |a| * bedCharge σ M+B)*K) ∧ AtomWall (ringT V.δ Q) η ((A + |a| * bedCharge σ M+B)*K) ∧ Bs G (ringT V.δ Q) ∧
      ∀ i, aperture (cents (m i)*ε i) (turnSeries (m:=m i) (ringT V.δ Q)) (U i-a • T i + W i) 1 :=by
   obtain ⟨w,K,hw,hs0,hK,H⟩:= siences G hG σ hs
   let p:= cut G w hw; let L:=credits G 1 (w-w/2)+1; have hL:1≤L:=by unfold L; linarith [waved (G:=G) (t:=1) (w-w/2)]
   refine ⟨p,w/2,K*L,by positivity,le_trans (half_le_self hw.le) hs0, by change w/2 < w; linarith, mul_nonneg hK (by linarith), fun m hm E T S A B M ε f g R i hA hB hM hε hR hV hv hF hQ=>?_⟩
   obtain ⟨X,⟨h,h'⟩,ht,hK⟩:=H m hm E T S A B M ε f g R i hA hB hM hε hR hV hv hF hQ
   obtain ⟨F,hf,hW⟩:=erect w (issue X) (story X) h
   let D:= (A+ |alphaPay i f| * bedCharge σ M +B)*K; have hv:F∈ p.s:= (silver hw F).2 (by rw [hf]; exact ⟨ht,h'⟩)
   obtain ⟨P,hP,he,hX⟩:= p.presented m (issue X) D ⟨F,hv,hW,hf.symm⟩; have hp:=silver hw P |>.1 (p.special m hP); let Y:=ringT w P; have hD : 0≤D:= (norm_nonneg _).trans he
   refine ⟨P,hP,he.trans (le_trans (le_mul_of_one_le_right hD hL) (by change _ ≤ _*(K*L); rw [←mul_assoc])),⟨?_,hp.2⟩,hp.1,fun i=>?_⟩
   · have H:=radius w P (show w/2<w by linarith) _ he; refine ⟨H.1,H.2.1,H.2.2.trans ?_⟩; change _ ≤ _*(K*L); rw [←mul_assoc (A+ |alphaPay i f| * _ + B) K L, mul_comm _ L]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hD
   specialize hK i -- remove
   unfold aperture noteAt beat; rw [← hX i]; exact hK

structure Reel (G:Gauge) where
    e2: Vow G 1
    e3: Vow G 2
    e4: Vow G 3
namespace Reel
variable (R: Reel G)
def Price (w:ℝ):= w<R.e2.δ ∧ w<R.e3.δ ∧ w<R.e4.δ
def Wing (c:ℕ→Side)(T:PathData G)(A L:ℝ):Prop:=∃ Q∈ R.e2.royal c, ‖Q‖≤ L ∧ T.loop=ringT R.e2.δ Q ∧ ∃ P∈ R.e3.royal c, ‖P‖≤ A ∧ T.cubic=ringT R.e3.δ P ∧ ∃ W∈ R.e4.royal c, ‖W‖≤ A ∧ T.quartic=ringT R.e4.δ W
end Reel
theorem pierce (G : Gauge) (hG : G.Simple) (σ w M Z : ℝ) (hs : 0<σ) (hw : 0<w) (hz : 0≤Z) :
    ∃ Ψ: Reel G, ∃ s K D : ℝ, 0<s ∧ s≤min σ w ∧ Ψ.Price s ∧ 0≤K ∧ 0≤D ∧ ∀ (c f : ℕ → Side), Tendsto (fun i => (c i).val) atTop atTop →
    ∀ (S : ∀ i, StepData (c i) (f i)) (F : ∀ i, Forest (S i).ratio) (t : ∀ i, (S i).Choices), (∀ i, Bid.Larger (G:=G) (S i)) →
    ∀ (p q : Clip) (B C : Bed) (U : PathData G) (ρ : ∀ i, Bid.Dir G (c i) → AxisChart G (F i)) (P : ChartRatio G) (μ τ A Λ η x y z u : ℝ), q.direct ≤ Z → LocalRatio P → 0<μ → 0<η →
      U.Bounds p τ A Λ → Attached B U → (∀ i, PriceGap (F i) p U η ∧ Critical (F i) p U (ρ i) ∧ Bid.HeatG (F i) p U (ρ i) C) →
      (∀ i, Floor B p (f i) x y ∧ Bid.Sworn B (f i) G) → (∀ n : Side, Floor C q n z u) → (∀ i, Bid.Sworn C (c i) G) →
      C.metric.strip w M → C.roots.strip w M →
    ∀ (L α : Picture G 1) (X Φ R : ℝ) (ε : ℕ → ℝ) (i : G.ColorIndex), Tendsto ε atTop (𝓝 0) → (∀ i, 0 ≤ ε i) → 1≤X →
      HasRecord (fun i=> victory (F i) (t i) p U (ρ i)) σ X 2 → HasRecord (fun i=> victory (F i) (t i) p U (ρ i)) σ X 3 →
      (∀ i j,Firm σ Φ (α i j) ∧ Firm σ R (L i j) ∧ Rays 4 (L i j ∘ axes)) →
      (∀ i, Recorded α (honorarium (F i) (t i) μ p U (ρ i)) (cents (c i)*ε i) ∧ Recorded L (burnished (F i) U (ρ i)) 0) →
    ∃ T : PathData G,
      T.row=rowPath C ∧ Attached C T ∧ (∀ s' A' Λ', 0<s' → s'≤s → rowPrice w M ≤ A' → X*K ≤ A' →
        (Φ + |alphaPay i α| * bedCharge (min σ w) M+R)*D ≤ Λ' → T.Bounds q s' A' Λ' ∧ Ψ.Wing c T A' Λ') ∧
      (∀ i, ClassicalMatch (F i) p q U T (ρ i)) ∧ ∀ j (Θ g Ω : ℝ), waveBank G*ε j ≤ Θ*Ω*Real.exp (-g * (c j).val) →
        FiniteBound (F j) U T p q (alphaPay i α) P (ρ j) Θ g Ω := by
  let s := min σ w
  have hS : 0<s := lt_min hs hw
  obtain ⟨V3,V4,a,K,ha,h₁,v₁,v₂,k,I⟩ := tanker G σ w M Z hs hw hz
  obtain ⟨V2,b,D,hb,h₂,v,d,Q⟩ := belleron G hG s hS
  refine ⟨⟨V2,V3,V4⟩,min a b,K,D,lt_min ha hb,(min_le_right ..).trans h₂, ⟨lt_of_le_of_lt (min_le_right ..) v,lt_of_le_of_lt (min_le_left ..) v₁,lt_of_le_of_lt (min_le_left ..) v₂⟩,k,d,?_⟩
  intro c f hm S F t h p q B C U ρ P μ τ A Λ η x y z u ht hP hg hη hu he H HY hF hx hW hR L α X Φ R ε i hε hv hX hh ho hK hz
  let f0 (i) := victory (F i) (t i) p U (ρ i)
  let f1 i := honorarium (F i) (t i) μ p U (ρ i)
  let f2 i := burnished (F i) U (ρ i)
  have hl j := campaign (H j).2.1 (h j).1 hu (t j) (H j).1 hη hg hP
  let V := blank C G
  have hf : V.Bounds q w (rowPrice w M) 0 := blank_cap hw hR (hF 1) le_rfl le_rfl
  obtain ⟨D3,z3,D4,z4,v3,v4,hD3,hD4,hE⟩ := I c hm C q z u hR (hF 1) ht f0 (fun i => (hl i).1) (fun j => violet (h j) (H j).2.1 (H j).2.2 hu he (HY j).1 (HY j).2 hf (rows_layout rfl) (hF _) (hx j) _) X hX hh ho
  have hp (j) := low_columns hf (rows_layout rfl) (hF _) (hx j)
  let i' : Ink G 2 := fun _ => i
  have hr := hK i' (fun _ => coord 0)
  have hM : 0 ≤ M := (price_step_metric hw hW (plaquette ⟨(0,1),by decide⟩) (plaquette ⟨(1,2),by decide⟩)).budget_nonneg
  obtain ⟨g,z2,v2,H',hx',Hz⟩ := Q c hm f1 f2 (fun j => inputSeries q V) Φ R M ε α L C.metric i hr.1.budget_nonneg hr.2.1.budget_nonneg hM hε (fun i j => (hW i j).mono (min_le_right ..) le_rfl) (hF 1).starts (fun i => ⟨(hl i).2.1,(hl i).2.2,stain_knit V q hf⟩) (fun i j=> ⟨(hK i j).1.mono hS (min_le_left ..) le_rfl,(hK i j).2.1.mono hS (min_le_left ..) le_rfl,(hK i j).2.2⟩) fun j => ⟨according (C.metric.rights w M hW hw.le) (hp j).2.2,hz j⟩
  let T := emitBase G C (ringT V2.δ g) (ringT V3.δ D3) (ringT V4.δ D4)
  let Z := (Φ + |alphaPay i α| * bedCharge (min σ w) M+R)*D
  have hΛ (s' A' Λ') (hp : 0<s') (hb : s'≤min a b) (hu : rowPrice w M ≤ A') (hz : X*K≤A') (hv : Z≤Λ') : T.Bounds q s' A' Λ' := by
    have hm : s'≤w := (hb.trans ((min_le_right ..).trans h₂)).trans (min_le_right ..)
    have hg := H'.mono (hb.trans (min_le_right ..)) hv
    exact build_cap C hp (fun i j => (hR i j).mono hm le_rfl) (hF 1) (le_trans (show rowPrice s' M ≤ rowPrice w M by unfold rowPrice; gcongr) hu) hg.1 (hD3.mono (hb.trans (min_le_left ..)) hz).1 (hD4.mono (hb.trans (min_le_left ..)) hz).1 (fun i => ⟨hg.2 _, hD3.2 _,hD4.2 _⟩) (fun i x => hx' i x T rfl)
  have hT := hΛ (min a b) (max (rowPrice w M) (X*K)) Z (lt_min ha hb) le_rfl (le_max_left ..) (le_max_right ..) le_rfl
  exact ⟨T,rfl,rows_layout rfl,fun s A Λ hp he hy hx h=>⟨hΛ _ _ _ hp he hy hx h,⟨g,z2,v2.trans h,rfl,D3,z3,v3.trans hx,rfl,D4,z4,v4.trans hx,rfl⟩⟩,fun j => achieved (h j).1 (H j).2.1 hu hT _ (H j).1 hη (hE (ringT V2.δ g) j),fun j Θ W Ω hg' => draft_pipe (t j) (H j).2.1 (h j).1 hu hT (H j).1 hη hg hP (hv j) (Hz j) _ _ _ hg'⟩

 end YM.Stationary
