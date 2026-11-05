import YM.UVExtension.Reward.Clocks

/-! Match tested heads using the included forest on each period, arbitrary labels. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Reward
open Lattice RG Supply Stationary Projection Precision Bloch Laurent Exterior Wilson Tree Filter Function Finset
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {s : Sheet G} {L : Rolls s} {Θ : Protection L} {a : Levels G}
    {P : MapPrices} {K V : Horizon a} {Z : ChartRatio G} {W : Delays Θ} {y : Bar W} {w : Wait y} {Q : PostCost L} {D : Knobs a} {ε : ℝ} {m N :ℕ}
variable {x : Cube G}

private lemma thumb (h : SatPath V N m (sat D V N m x))(hp: m≤N)(hi: Working D V P m) (j : ℕ) (v : Fin 2→ Link G (a.S.side m j)):
    iteratedFDeriv ℝ 2 (inputSeries (a.params m).clip (sat D V N m x)) 0 v= reading (label D m) (V.H N m) j v:=by
  have he:=hi.beside N hp
  have hL:=low_columns h.bound h.ties (he.2.2.1 _) (he.2.2.2 j)
  rw [show v=![v 0,v 1] from funext fun i=> by fin_cases i <;> rfl]; exact hL.2.2 _ _

lemma keysReady (h : Working D V P m)(hp:m ≤ N):Keyline (label D m) (V.H N m):=by
  have ht:=h.beside N hp
  refine ⟨⟨P.α _,_, P.alpha_pos _,ht.1⟩,(ht.2.2.1 1).starts,fun i x y=>?_⟩
  have hx := h.paid N hp 0 (Submodule.zero_mem _) (by simp)
  rw [← thumb hx hp h,← thumb hx hp h]; apply Work.F03.hessian_symmetric ((stain_knit _ _ hx.bound).analytic.contDiffAt)

-- freeze labels of S uniformly
abbrev treeAt (a:Levels G)(m p:ℕ): Forest (a.clock.op m p).ratio:= Classical.choice (Tree.select _ (a.S.block_odd m))
abbrev turnAt (a:Levels G)(m p:ℕ) : (a.clock.op m p).Choices:=Classical.arbitrary _
abbrev testF (R:PathData G)(z:GainWire a m)(p:ℕ): Bid.Dir G (a.S.side m p)→ℝ:= fun x=> tested (treeAt a m p) (turnAt a m p) (a.params (m+1)).clip R x (z p _ x)
abbrev testL (Z : ChartRatio G)(R:PathData G)(z:GainWire a m)(p:ℕ): Bid.Dir G (a.S.side m p)→ℝ:= thermal (treeAt a m p) (turnAt a m p) (a.params (m+1)).clip R (z p _) Z

def airF (D : Knobs a) (B : Bed)(R : PathData G)(z:GainWire a m):Head (label D m):= fun i j v=>
    iteratedFDeriv ℝ (j:ℕ) (testF R z i ∘ arm G (a.S.side m i) 1) 0 v - iteratedFDeriv ℝ (j:ℕ) (inputSeries (a.params m).clip ((label D m).path B 0)) 0 v

def airL (D:Knobs a)(Z:ChartRatio G)(R:PathData G)(z:GainWire a m):Stamp (label D m):=fun i v=>
    iteratedFDeriv ℝ 2 (testL Z R z i ∘ arm G (a.S.side m i) 1) 0 v

lemma classOrder {R α z} (h : Bubble V Q Z N m R (sat D V N m x) α z): traceHead (label D m) (x,α)= airF D (V.H N m) R z:=by
  funext i j v
  let S := a.S.side m i; let t := (a.params m).clip; let E:=label D m; let B:= sat D V N m x
  let W:= inputSeries t B (m:=S); let Gt : Link G S → ℝ:= E.hat x i
  have hw :ContDiffAt ℝ (j:ℕ) W 0:= (stain_knit _ _ h.lives.bound).analytic.contDiffAt
  have ht:= (h.steps i (treeAt a m i)).2.2.2.1 j (by have hh:=j.isLt; omega) (turnAt a m i)
  let l := fun y:Bid.Dir G S=> mainTerm t B (represent y)
  have hh : testF R z i ∘ arm G S 1 = (testF R z i) ∘ (arm G S 1).toContinuousLinearMap:=rfl
  have hf: iteratedFDeriv ℝ (j:ℕ) (testF R z i ∘ arm G S 1) 0 v= iteratedFDeriv ℝ (j:ℕ) (l ∘ arm G S 1) 0 v :=by
    let L:=(arm G S 1).toContinuousLinearMap
    change iteratedFDeriv ℝ _ (testF R z i∘ L) _ _=iteratedFDeriv ℝ _ (l∘ L) _ _
    have hg : SameJet j (testF R z i) l:= ht
    rw [wired L (by rw [map_zero]; exact hg.1.analyticAt),wired L (by rw [map_zero]; exact hg.2.1.analyticAt),map_zero,hg.2.2]
  have hu : l ∘ arm G S 1= W + Gt:= by change intended _ _=_; rw [intent,add_assoc]; rfl
  unfold airF; rw [hf,hu, iteratedFDeriv_add_apply hw (show ContDiffAt ℝ (j:ℕ) Gt 0 from (E.hat_an x i).contDiffAt),_root_.add_apply]; exact Eq.symm (add_sub_cancel_left (iteratedFDeriv ℝ (j:ℕ) W 0 v) _)

def tariff {a:Levels G}(Q:PostCost L)(m:ℕ) (i:ℕ): ℝ:= Q.Γ (a.clock.J (m+1))* Real.exp (-Q.c (a.clock.J (m+1))*(a.S.side m i).val)
lemma levity (_D:Knobs a):Tendsto (tariff (a:=a) Q m) atTop (𝓝 0):=mesh_tend _ (bound_climb G a m) (Q.posC _)

lemma mistOrder {R α z}(hp: Working D V P m) (hr: m<N) (h : Bubble V Q Z N m R (sat D V N m x) α z) (i j k) (u v: HatWave G)(hx: ValidPitch u)(hy:ValidPitch v):
    ‖(amount (label D m) (V.H N m) (x,α) - airL D Z R z) i ![pew j u,pew k v]‖ ≤ cents ((label D m).stageSide i) *tariff (a:=a) Q m i:=by
  let E:= label D m; let S:= a.S.side m i; let p:=(a.params m).clip
  let M:=arm G S 1; let T:= sat D V N m x; let L:=inputSeries p T (m:=S);
  let w:=( ![pew j u,pew k v]:Fin 2→Link G S); let w' := (![wave j u,wave k v]:Fin 2→Bid.Dir G S)
  let H:=draft α T p (c:=S)
  let b:=testL Z R z i
  have he:= (h.steps i (treeAt a m i)).2.2.2.2
  have hE : ContDiffAt ℝ ω (H ∘ M) 0:= (show ContDiffAt ℝ ω H (M 0) from (by rw [map_zero]; exact he.classicalResult)).comp _ M.contDiff.contDiffAt
  have hh: iteratedFDeriv ℝ 2 b 0 w'=airL D Z R z i w:= wired_wave ( (show ContDiffAt ℝ ω b (M 0) from (by rw [map_zero]; exact he.born _)).comp (f:=M) 0 M.contDiff.contDiffAt ) _ _ _ _
  have hH: iteratedFDeriv ℝ 2 H 0 w'= amount E (V.H N m) (x,α) i w:=by
    rw [show iteratedFDeriv ℝ 2 H 0 w'= _ from wired_wave hE j k u v]
    let U : Link G S → ℝ := E.eHat x i
    change iteratedFDeriv ℝ 2 ((α • L)+ U) 0 w=_
    have hf: ContDiffAt ℝ 2 L 0:= (stain_knit _ _ h.lives.bound).analytic.contDiffAt
    have hz: ContDiffAt ℝ 2 (α • L) 0:= hf.const_smul α
    rw [iteratedFDeriv_add_apply hz (show ContDiffAt ℝ 2 U 0 from (turns_analytic T.loop (m:=S) h.lives.bound.width h.lives.bound.two).contDiffAt),iteratedFDeriv_const_smul_apply hf,_root_.add_apply, _root_.smul_apply] -- refine
    rw [show iteratedFDeriv ℝ 2 L 0 w= _ from thumb h.lives hr.le hp i w]; rfl
  change ‖amount E _ _ i w-airL _ _ _ _ i w‖≤_; rw [← hH,← hh,Real.norm_eq_abs,abs_sub_comm]; unfold tariff
  rw [← mul_assoc]; simpa only [mul_one] using! he.wave_price (turnAt a m i) j k u v hx hy

lemma aligned {R:PathData G}{ρ:GainWire a m}{α:ℝ}(h : Courtesy V D Q Z ε N m R x α ρ)(he: m<N)(ht:Working D V P m): Aligns (label D m) (V.H N m) (x,α) (airF D (V.H N m) R ρ) (airL D Z R ρ):= ⟨(paints_iff ..).2 h.above,classOrder h.bubble, (show Neglect _ _ from ⟨_,levity D, mistOrder ht he h.bubble⟩) ⟩
end YM.UVExtension.Reward
