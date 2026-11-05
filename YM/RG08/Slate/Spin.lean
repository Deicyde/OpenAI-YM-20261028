import YM.RG08.Slate.Turn
/-!
# Taxative conversion of the transformation: incumbent integrated area determinant
 after centering
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Slate
open Filter Function Matrix MeasureTheory Lattice Exterior Wilson RG Precision Stationary Work.F05 Tree Prism Tack Camera
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {I X Y J:Type}[Fintype I][Fintype X][Fintype Y]
variable (M:Cellar (Raw I X) → Cellar (Raw I Y))
def lagoon (x:Cellar X)(t:Cellar I):Cellar I:= internal (M (merge t x))
private def fell : Cellar I →L[ℝ] Cellar (Raw I X):= ContinuousLinearMap.pi (Sum.elim (fun i=>ContinuousLinearMap.proj i) (fun _=>0))
private lemma blood (x:Cellar X)(t:Cellar I):HasFDerivAt (fun z=>merge z x) (fell (I:=I) (X:=X)) t:=by
 let a:= fell (I:=I) (X:=X)
 have he: (fun z:Cellar I=> merge z x)=(fun z=>a z+merge (0:Cellar I) x):=by funext z i;cases i <;>simp [merge,fell,a]
 rw [he]; exact a.hasFDerivAt.add_const _
lemma send {x:Cellar (Raw I X)}(ht:DifferentiableAt ℝ M x) : Fold.Peak.rated (fun (i:Raw I Y)(z:Cellar (Raw I X))=> M z i) x= (fderiv ℝ (lagoon M (envar x)) (internal x)).det:=by
 let c:=envar x; let u:= internal x
 let L:= fderiv ℝ (lagoon M c) u
 unfold Fold.Peak.rated; change _= LinearMap.det L.toLinearMap
 rw [← LinearMap.det_toMatrix' L.toLinearMap]
 congr 1; ext i j;rw [LinearMap.toMatrix'_apply,Matrix.of_apply]
 let R:=ContinuousLinearMap.proj (φ:=fun _ : Raw I Y=>ℝ) (R:=ℝ) (.inl i)
 have hv(i:I) : (Camera.billet (I:=Raw I X) (.inl i)) =fell (I:=I) (X:=X) (Pi.single i 1):=by -- name f
    ext (a|a) <;>simp [fell,Pi.single_apply,Camera.billet]
 let G:= ContinuousLinearMap.proj (φ:=fun _ : I=>ℝ) (R:=ℝ) i
 let H(v:Cellar I):=M (merge v c)
 have hT: DifferentiableAt ℝ M (merge u c):= (splice x).symm ▸ ht
 have hb : HasFDerivAt (fun t=> R (M (merge t c))) (R ∘L ((fderiv ℝ M x) ∘L fell)) u:=by
    have H0:=R.hasFDerivAt.comp u (hT.hasFDerivAt.comp u (blood c u))
    rw [show merge u c=x from splice x] at H0;exact H0
 let V : Cellar (Raw I Y) →L[ℝ] Cellar I:=ContinuousLinearMap.pi fun i=>ContinuousLinearMap.proj (.inl i)
 have hh:DifferentiableAt ℝ (lagoon M c) u:= V.differentiableAt.comp u (hT.comp u (blood c u).differentiableAt)
 have he: HasFDerivAt (fun t=> R (M (merge t c))) (G ∘L L) u:=G.hasFDerivAt.comp (f:=lagoon M c) u hh.hasFDerivAt
 have hx:=hb.unique he
 change (fderiv ℝ _ _) (Camera.billet (Sum.inl j:Raw I X))=_;rw [hv]
 change (fderiv ℝ (R ∘ M) x) _=G (L _)
 rw [fderiv_comp _ R.differentiableAt ht, R.fderiv]; exact DFunLike.congr_fun hx _

-- center by block shifts & viola, Jacobian frozen at those coordinates.
variable {G: Gauge}{c f:Side}(S: StepData c f)(F: Forest S.ratio)(A B : Bed)
variable (v:Lines G c 1→X)(w:Lines G c 1→Y)
def scene (g:Cellar X→Cellar Y)(m:Cellar X→ AxisChart G F→AxisChart G F):Strip (Raw (Key F G) Y) (Raw (Key F G) X):=fun i t=> Slate.flight S F A B v m w g t i
variable (g:Cellar X→Cellar Y)(m:Cellar X→ AxisChart G F→AxisChart G F)
lemma dues (x:Lex F G X)(hf:DifferentiableAt ℝ (Slate.flight S F A B v m w g) x)(hm:DifferentiableAt ℝ (m (envar x)) (frock F A B v x)):
 Fold.Peak.rated (scene S F A B v w g m) x= (fderiv ℝ (m (envar x)) (frock F A B v x)).det:=by
 let f:= Slate.flight S F A B v m w g;let c:=envar x;let y := frock F A B v x
 let η:=fderiv ℝ (m c) y
 let V:=viola S F (G:=G)
 have he : HasFDerivAt (lagoon f c) (V.symm.toContinuousLinearMap ∘L (η ∘L V.toContinuousLinearMap)) (internal x):=by
    have hh : HasFDerivAt (fun t=>frock F A B v (merge t c)) V.toContinuousLinearMap (internal x):=by
       have H:(fun t=>frock F A B v (merge t c))=fun t=>V t+bowl S F A B v c:= by funext t; rw [Slate.proffer]; rfl
       rw [H]; exact V.toContinuousLinearMap.hasFDerivAt.add_const _
    have hb : HasFDerivAt (fun t=> m c (frock F A B v (merge t c))) (η ∘L V.toContinuousLinearMap) (internal x):=by
       apply HasFDerivAt.comp (g:=m c) (f:=fun t=>_) _ _ hh; rw [show frock F A B v (merge (internal x) c)=y from congrArg _ (splice x)]; exact hm.hasFDerivAt
    exact V.symm.toContinuousLinearMap.hasFDerivAt.comp (internal x) (hb.sub_const (bowl S F A B w (g c)))
 -- det class mismatch Key F etc? send implicit det uses Classical with Key vs proof. compare via wrapper.
 have H :LinearMap.det (V.symm.toContinuousLinearMap ∘L (η ∘L V.toContinuousLinearMap)).toLinearMap=η.det:=LinearMap.det_conj η.toLinearMap V.toLinearEquiv.symm
 unfold scene
 rw [send _ hf,he.fderiv]; exact H
variable {Z:ChartRatio G}
lemma duefy (P:Cellar X→ House F (G:=G) F)(h:LocalRatio Z)(hm:Pace (uncurry m))(hg:Pace g)(h0:g 0=0)(hw:m 0 0=0)(he:∀ᶠ z:Cellar X×AxisChart G F in 𝓝 0, exposure F 0 (m z.1 z.2)= (P z.1).arrow (exposure F 0 z.2)):
 trophy F A B v Z=ᶠ[𝓝 0] fun t=> trophy F A B w Z (roll (scene S F A B v w g m) t)* |Fold.Peak.rated (scene S F A B v w g m) t|:=by
 let f(t:Lex F G X):=(envar t,frock F A B v t)
 have ht0:f 0=0:=by unfold f;rw [central];rfl
 have ht:Tendsto f (𝓝 0) (𝓝 0):=by simpa only [ht0] using! (show Pace f from smooth2.contDiffAt.prodMk (frock_pace ..)).continuousAt.tendsto
 have hh:= (flying S F A B v m w g hm hg h0).eventually (by simp)
 have hM:= ht.eventually (hm.eventually (by simp))
 filter_upwards [ht.eventually (network F P m h hm hw he),hh,hM] with x hx hy hA
 let z:=envar x;let y:=frock F A B v x
 have hT : DifferentiableAt ℝ (m z) y:= (hA.differentiableAt (by simp)).comp y ((differentiableAt_const _).prodMk differentiableAt_id)
 unfold trophy Camera.roll Function.comp
 rw [show (fun i => scene S F A B v w g m i x)=Slate.flight S F A B v m w g x from rfl,dues _ _ _ _ _ _ _ _ _ (hy.differentiableAt (by simp)) hT,paid]
 exact hx
end YM.RG08.Slate
