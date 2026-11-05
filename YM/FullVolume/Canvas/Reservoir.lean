import YM.FullVolume.Canvas.Edit
/-! adapt classical assembly.V.P.Age of historical requisitions.Bounded with issued paths. Use Stand.Vow within fixed level call. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary
open Shade Function Lattice RG Exterior Wilson Precision Bloch Laurent Filter Finset Asymptotics Metric
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {m : Side} {σ A Λ : ℝ} {n t : ℕ}
private lemma busQ (G : Gauge) (σ : ℝ) (hs : 0<σ) (t : ℕ) [NeZero t] (ht : 2 ≤ t) :
    ∃ w D : ℝ, 0<w ∧ w≤σ ∧ 0 ≤ D ∧ ∀ m : ℕ → Side, Tendsto (fun i => (m i).val) atTop atTop →
    ∀ (F : ∀ i, Link G (m i) → ℝ) (A : ℝ), (∀ i, Pointwise (F i)) → (∀ i, Rays (t+1) (F i)) →
      0≤A → HasRecord F σ A t → ∃ R:Skin G t, AtomWall (issue R) w (A*D) ∧ ∀ i,
        Rays (t+2) (F i-turnSeries (issue R)) := by
  obtain ⟨η,K,hp,he,hK,H⟩ := strokes G t ht σ hs
  refine ⟨η,K*inkCost G t η,hp,he,mul_nonneg hK (inkCost_nonneg ..),fun m hM F A hh ht ha hR => ?_⟩
  obtain ⟨L,hL,Hm⟩ := hR
  obtain ⟨a,g⟩ := H A L ha (withdrew hM (tendsto_const_nhds (x:=(0:ℝ))) hL (fun i => by simpa only [mul_zero] using (Hm i))
    (fun i => (hh i).analytic) (fun i => (hh i).stained) (fun i => (hh i).guard) (fun i j hj _ =>
      (rays_jet (hh i).analytic _).mp (ht i) j hj))
  obtain ⟨hi,hv⟩ := artery_funded g
  refine ⟨a, ⟨?_, hv⟩,fun i => ?_⟩
  · rw [← mul_assoc]; exact hi
  let R := F i-turnSeries (issue a)
  have hV := stain_ink (issue a) hp hi hv (m:=m i)
  have hX := ((hh i).sub hV).analytic
  have hlow : Rays (t+1) R := (ht i).sub (turns_low _ hp hi)
  refine (rays_jet hX _).2 fun j hj => ?_
  rcases eq_or_lt_of_le (Nat.le_of_lt_succ hj) with h|h
  · rw [h,iteratedFDeriv_sub_apply (hh i).analytic.contDiffAt hV.analytic.contDiffAt]
    exact sub_eq_zero.mpr (aperture_eq (colors_align (F i) (hh i).analytic (hh i).lights L a g hp (Hm i))).symm
  exact (rays_jet hX _).1 hlow j h

private lemma oracle (G:Gauge)(σ:ℝ)(hp:0<σ)(t:ℕ)[NeZero t](ht:2≤t): ∃ (V:Vow G t) (w C:ℝ),0<w ∧ w≤σ ∧ w<V.δ ∧ V=core G t V.δ V.hired ∧ 0≤C ∧ ∀ m:ℕ→Side,Tendsto (fun i=>(m i).val) atTop atTop → ∀ (F:∀ i,Link G (m i)→ℝ) (A:ℝ),(∀ i,Pointwise (F i))→ (∀ i,Rays (t+1) (F i))→ 0≤A→ HasRecord F σ A t→
   ∃ W∈ V.royal m, ‖W‖ ≤ A*C ∧ AtomWall (ringT V.δ W) w (A*C) ∧ ∀ i,Rays (t+2) (F i-turnSeries (ringT V.δ W)):=by
     obtain ⟨w,C,h,h1,hC,Q⟩:= busQ G σ hp t ht
     let Y:= core G t w h; let L:= credits G t (w-w/2)
     have hL : 0 ≤ L:= waved ..
     have hv:w/2<w:= by linarith
     refine ⟨Y,w/2,(1+L)*C,by positivity,hv.le.trans h1,hv,rfl,mul_nonneg (by linarith) hC,fun m hm F A hX hR hA hx=>?_⟩
     obtain ⟨T,hT,he⟩:= Q m hm F A hX hR hA hx
     obtain ⟨P,hP,hp⟩:= erect w (issue T) (story T) hT.1
     obtain ⟨D,hD,hd,hx⟩:=Y.presented m (issue T) (A*C) ⟨P,(gold h P).2 (by rw [hP]; exact hT.2),hp,hP.symm⟩
     let W:=ringT w D
     have hh : AtomWall W (w/2) (A*((1+L)*C)):=by
          have hs:= radius w D hv (A*C) hd
          refine ⟨⟨hs.1,hs.2.1,hs.2.2.trans ?_⟩, (gold h D).1 hD.1⟩
          change L*(A*C)≤ A*_; nlinarith only [mul_nonneg hA hC]
     refine ⟨D,hD,hd.trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hC (by linarith)) hA),hh,fun i=>?_⟩
     have ha: AnalyticAt ℝ (F i-turnSeries (ringT w D)) 0:= (hX i).analytic.sub (shineN h)
     refine (rays_jet ha _).2 fun j hj=>?_
     obtain hj|Hj := lt_or_eq_of_le (show j ≤ t+1 by omega)
     · exact (rays_jet ha _).1 ((hR i).sub (turns_low _ (half_pos h) hh.1)) _ hj
     subst j
     rw [iteratedFDeriv_sub_apply (hX i).analytic.contDiffAt (shineN h|>.contDiffAt),← show iteratedFDeriv ℝ (t+1) (turnSeries (issue T)) _= iteratedFDeriv ℝ _ (turnSeries (ringT w D)) _ from hx i,
         ← iteratedFDeriv_sub_apply (hX i).analytic.contDiffAt (turns_analytic _ h hT.1 |>.contDiffAt)]; exact (rays_jet ((hX i).analytic.sub (turns_analytic _ h hT.1)) _).1 (he i) _ (by omega)
lemma tinted (G : Gauge) (σ : ℝ) (hp : 0<σ) : ∃ (V3:Vow G 2) (V4:Vow G 3) (η C:ℝ), 0<η ∧ η ≤ σ ∧ η<V3.δ ∧ η<V4.δ ∧ 0 ≤ C ∧ ∀ m : ℕ → Side,
    Tendsto (fun i => (m i).val) atTop atTop → ∀ (F : ∀ i, Link G (m i)→ℝ),
      (∀ i, Pointwise (F i)) → (∀ i, Rays 3 (F i)) → ∀ A, 0 ≤ A → HasRecord F σ A 2 → HasRecord F σ A 3 →
    ∃ X∈ V3.royal m,∃ V∈ V4.royal m, ‖X‖≤ A*C ∧ ‖V‖≤ A*C ∧ AtomWall (ringT V3.δ X) η (A*C) ∧ AtomWall (ringT V4.δ V) η (A*C) ∧
      ∀ i, Rays 5 (F i-turnSeries (ringT V3.δ X)-turnSeries (ringT V4.δ V)) := by
  obtain ⟨V3,w,K,hk,hu,hk',HΞ,hK,H⟩ := oracle G σ hp 2 (by decide)
  obtain ⟨τ,B,hτ,hB,I⟩ := orbit_cost G 3 3 hk
  let a := min σ τ
  have ha : 0<a := lt_min hp hτ
  obtain ⟨V4,v,b,hv,hx,hv',he,hb,L⟩ := oracle G a ha 3 (by decide)
  let c := (1+K*B)*b
  have hc : 0 ≤ c := by unfold c; positivity
  refine ⟨V3,V4,min w v, K+c, lt_min hk hv,(min_le_left ..).trans hu,lt_of_le_of_lt (min_le_left ..) hk', lt_of_le_of_lt (min_le_right ..) hv',add_nonneg hK hc,fun m hm F hg hh A hA hF hG => ?_⟩
  obtain ⟨X,hχ,hχ',HX,Hz⟩ := H m hm F A hg hh hA hF
  obtain ⟨D,hd,HD⟩ := I (ringT V3.δ X) (A*K) HX.1
  let E i := turnSeries (ringT V3.δ X) (m:=m i)
  have he i : Pointwise (E i) := stain_ink (ringT V3.δ X) hk HX.1 HX.2
  have hy : HasRecord E a (A*K*B) 3 := HasRecord.mono (show HasRecord E τ (A*K*B) 3 from ⟨D,hd,fun i => HD _⟩) ha (min_le_right ..) le_rfl
  obtain ⟨Y,hξ,hξ',hY,U⟩ := L m hm (F-E) _ (fun i => (hg i).sub (he i)) Hz (by positivity)
    (((hG.mono ha (min_le_left ..) le_rfl)).sub hy (fun i => (hg i).analytic) (fun i => (he i).analytic))
  have hY' : AtomWall (ringT V4.δ Y) v (A*c) := by
    rw [show A*c=(A+A*K*B)*b by unfold c; ring]; exact hY
  exact ⟨X,hχ,Y,hξ,hχ'.trans (mul_le_mul_of_nonneg_left (by linarith) hA), hξ'.trans (le_trans (Eq.le (show (A+A*K*B)*b=A*c by unfold c; ring)) (mul_le_mul_of_nonneg_left (by linarith) hA)),HX.mono (min_le_left ..) (by gcongr; linarith),hY'.mono (min_le_right ..) (by gcongr; linarith), U⟩

/-- Operates subtracting at same chart and real metric; buys support at the width
chosen from the target widths and free input H phase prices. `M≥1` is the jet
budget in sup. -/
lemma tanker (G : Gauge) (σ σ₀ : ℝ) (A Z : ℝ) (hs : 0<σ) (hσ : 0<σ₀) (hz : 0≤ Z) :
    ∃ (V3:Vow G 2)(V4:Vow G 3)(τ C:ℝ), 0<τ∧ τ≤σ∧ τ<V3.δ ∧ τ<V4.δ ∧ 0≤C ∧ ∀ (m : ℕ → Side), Tendsto (fun i => (m i).val) atTop atTop →
      ∀ (B : Bed) (p : Clip) (a b : ℝ), B.roots.strip σ₀ A → Floor B p 1 a b → p.direct ≤ Z → ∀ E : ∀ i, Link G (m i) → ℝ, (∀ i, Pointwise (E i)) →
        (∀ i, Rays 3 (E i - inputSeries p (blank B G))) → ∀ M : ℝ, 1 ≤ M → HasRecord E σ M 2 → HasRecord E σ M 3 →
      ∃ X∈ V3.royal m,∃ V∈ V4.royal m, ‖X‖≤ M*C ∧ ‖V‖≤ M*C ∧ AtomWall (ringT V3.δ X) τ (M*C) ∧ AtomWall (ringT V4.δ V) τ (M*C) ∧
        ∀ f : ℕ → Atom G 2, ∀ i, Rays 5 (E i - intended p (emitBase G B f (ringT V3.δ X) (ringT V4.δ V))) := by
  let k := rowPrice σ₀ A
  obtain ⟨v,P,hv,hP,H⟩ := column_price G 2 k Z hσ hz
  obtain ⟨w,Q,hw,hQ,Y⟩ := column_price G 3 k Z hσ hz
  let a := min σ (min v w)
  have hb : a≤σ := min_le_left ..
  have hh : a≤v := (min_le_right ..).trans (min_le_left ..)
  have he : a≤w := (min_le_right ..).trans (min_le_right ..)
  have ha : 0 < a := lt_min hs (lt_min hv hw)
  obtain ⟨V3,V4,x,J,hx,hX,Hq,Hq',hJ,D⟩ := tinted G a ha
  refine ⟨V3,V4,x,(1+(P+Q))*J,hx,hX.trans hb,Hq,Hq',by positivity,fun m hm B p b z hB hu hp E hE hl M hM HF HG => ?_⟩
  have h0 : 0≤M := zero_le_one.trans hM
  let W := blank B G
  have hW : W.Bounds p σ₀ k 0 := blank_cap hσ hB hu le_rfl le_rfl
  have hc : BankRows W σ₀ k := hW.rows
  obtain ⟨ht,U,hU,hU'⟩ := H p _ _ _ _ hp hW hc
  obtain ⟨hα,S,hS,hS'⟩ := Y p _ _ _ _ hp hW hc
  let F i := inputSeries p W (m:=m i)
  have hs i : Pointwise (F i) := stain_knit _ _ hW
  have hm' : HasRecord F v P 2 := ⟨U,hU,fun i => hU' _⟩
  have hm'' : HasRecord F w Q 3 := ⟨S,hS,fun i => hS' _⟩
  obtain ⟨X,z1,V,z2,w1,w2,h₁,h₂,h₃⟩ := D m hm (E-F) (fun i => (hE i).sub (hs i)) hl (M+P+Q) (by positivity)
    ((((HF.mono ha hb le_rfl)).sub (hm'.mono ha hh le_rfl) (fun i => (hE i).analytic) (fun i => (hs i).analytic)).mono ha le_rfl (by linarith))
    ((((HG.mono ha hb le_rfl)).sub (hm''.mono ha he le_rfl) (fun i => (hE i).analytic) (fun i => (hs i).analytic)).mono ha le_rfl (by linarith))
  have hC : (M+P+Q)*J ≤ M*((1+(P+Q))*J) := by rw [← mul_assoc]; gcongr; nlinarith [mul_nonneg (sub_nonneg.mpr hM) (add_nonneg hP hQ)]
  refine ⟨X,z1,V,z2,w1.trans hC,w2.trans hC,h₁.mono le_rfl hC,h₂.mono le_rfl hC,fun f i => ?_⟩
  rw [intent]
  convert h₃ i using 1
  change _- (F i + turnSeries (ringT V3.δ X) + turnSeries (ringT V4.δ V))=E i-F i-_-_
  abel

end YM.Stationary
