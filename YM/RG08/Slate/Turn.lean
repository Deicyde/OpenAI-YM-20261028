import YM.RG08.Slate.Centric

/-! # Centered coordinates bridge, keep both external flows same chart and no
    assumptions on derivative of optical cost ; chart shifts & ratios normalized on
    every integration site. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Slate
open Filter Function Matrix MeasureTheory Lattice Exterior Wilson RG Precision Stationary Work.F05 Tree Prism Tack Camera
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}(S:StepData c f)(F:Forest S.ratio){Z:ChartRatio G}
variable (A B: Bed){X:Type}[Fintype X](v:Lines G c 1→X)

def viola :Cellar (Precision.Key F G)≃L[ℝ]AxisChart G F := LinearEquiv.toContinuousLinearEquiv {
 toFun a i:=WithLp.toLp 2 fun j=> a (i,j)
 invFun a i:=a i.1 i.2
 left_inv _:=rfl
 right_inv _:=rfl
 map_add' _ _:=rfl
 map_smul' _ _:=rfl}
lemma tin (x:Cellar (Precision.Key F G))(i)(j): viola S F x i j=x (i,j):=rfl
variable {I Y:Type}[Fintype I][Fintype Y]

def internal (x:Cellar (Raw I X)):Cellar I:=x ∘ Sum.inl
def envar (x:Cellar (Raw I X)):Cellar X:=x ∘ Sum.inr
def merge (x:Cellar I)(y:Cellar X):Cellar (Raw I X):=Sum.elim x y
omit [Fintype X] [Fintype I] in
lemma splice [Fintype X] [Fintype I] (x:Cellar (Raw I X)):merge (internal x) (envar x)=x:=by funext i; cases i<;>rfl
lemma linking : ContDiff ℝ ω (uncurry (merge (I:=I) (X:=X))):=by refine contDiff_pi.mpr ?_; rintro (i|i);exact (contDiff_apply ℝ _ i).comp contDiff_fst;exact (contDiff_apply ℝ _ i).comp contDiff_snd
lemma smooth1 :ContDiff ℝ ω (internal (I:=I) (X:=X)):=contDiff_pi.mpr (fun i=>contDiff_apply ℝ ℝ (Sum.inl i))
lemma smooth2 :ContDiff ℝ ω (envar (I:=I) (X:=X)):=contDiff_pi.mpr (fun i=>contDiff_apply ℝ ℝ (Sum.inr i))

def bowl (w:Cellar X) : AxisChart G F:=frock F A B v (merge 0 w)
lemma proffer (x:Lex F G X):frock F A B v x=viola S F (internal x)+bowl S F A B v (envar x):=by
 let D:=grace G S F A B
 let J:= speak D (fir S) v
 have he: Proceed.wx S (J *ᵥ x)= iris G S F *ᵥ internal x+D.mean *ᵥ (envar x ∘ v):= (speak_zone D (fir S) v x).1
 have hh(u:Tree.Forest.Free F)(j:G.ColorIndex)(x:Lex F G X): frock F A B v x u j=Proceed.wx S (J*ᵥ x) (pore G S F (u,j)):=rfl
 ext i j
 change _=viola S F (internal x) i j+bowl S F A B v _ i j
 rw [hh i j,he,Pi.add_apply,frost,tin,bowl,hh]
 have hv:= (speak_zone D (fir S) v (merge (0:Cellar (Precision.Key F G)) (envar x))).1
 change Proceed.wx S (J *ᵥ _) = _ at hv;rw [hv,Pi.add_apply, show (merge (0:Cellar (Precision.Key F G)) _ ∘ Sum.inl)=(0:Cellar (Precision.Key F G)) from rfl,mulVec_zero,Pi.zero_apply,zero_add]; rfl
lemma bowl_pace : Pace (bowl S F A B v) := by
 have hz : merge (0 : Cellar (Precision.Key F G)) (0 : Cellar X) = 0 := by
   funext i; cases i <;> rfl
 have hf : ContDiffAt ℝ ω (frock F A B v) (merge 0 (0 : Cellar X)) := hz.symm ▸ frock_pace F A B v
 exact hf.comp (f:=fun x => merge 0 x) 0 ((linking.comp (contDiff_const.prodMk contDiff_id)).contDiffAt)
lemma bowl_center:bowl S F A B v 0=0:=by
 unfold bowl
 rw [show merge (0:Cellar (Precision.Key F G)) (0:Cellar X)=0 from by ext i; cases i<;>rfl,central]

def call (t:Cellar Y)(u:AxisChart G F): Cellar (Raw (Key F G) Y):=merge ((viola S F).symm u) t

def flight (M:Cellar X→AxisChart G F→AxisChart G F) (w:Lines G c 1→Y) (g:Cellar X→Cellar Y)(x:Lex F G X):Lex F G Y:=
 call S F (g (envar x)) (M (envar x) (frock F A B v x)-bowl S F A B w (g (envar x)))
lemma paid (M:Cellar X→AxisChart G F→AxisChart G F)(w:Lines G c 1→Y)(g:Cellar X→Cellar Y)(x:Lex F G X):
 frock F A B w (flight S F A B v M w g x)=M (envar x) (frock F A B v x):=by
 rw [proffer S F A B w]
 change (viola S F) ((viola S F).symm (_-bowl S F A B w (g (envar x))))+ bowl S F A B w (g (envar x))=_
 rw [ContinuousLinearEquiv.apply_symm_apply,sub_add_cancel]

variable (M:Cellar X→AxisChart G F→AxisChart G F) (w:Lines G c 1→Y) (g:Cellar X→Cellar Y)

lemma flying (hm:Pace (uncurry M))(hg:Pace g)(h0:g 0=0): Pace (flight S F A B v M w g):=by
 have hh:Pace (g ∘ envar (I:=Precision.Key F G)):= hg.comp 0 smooth2.contDiffAt
 have hz:(g ∘ envar (I:=Precision.Key F G)) (0:Lex F G X)=0:=by rw [Function.comp_apply,show envar (0:Lex F G X)=(0:Cellar X) from rfl,h0]
 have ht: Pace (bowl S F A B w ∘ g ∘ envar (I:=Precision.Key F G)):= ContDiffAt.comp (0:Lex F G X) (g:=bowl S F A B w) (hz.symm ▸ bowl_pace S F A B w) hh -- eq orientation
 let a (x : Lex F G X):= (envar x, frock F A B v x)
 have he:a 0=0:=by unfold a;rw [central];rfl
 have hv:Pace (uncurry M ∘ a):= ContDiffAt.comp _ (g:=uncurry M) (he.symm ▸ hm) (smooth2.contDiffAt.prodMk (frock_pace ..))
 apply (((linking (I:=Precision.Key F G) (X:=Y)).contDiffAt).comp (f:=fun x:Lex F G X=>((viola S F).symm ((uncurry M ∘ a) x-(bowl S F A B w ∘ g ∘ envar) x),g (envar x))) _ (((viola S F).symm.contDiff.contDiffAt.comp (f:=fun x=> (uncurry M ∘ a) x-(bowl S F A B w ∘ g ∘ envar) x) _ (hv.sub ht)).prodMk hh))
lemma start(h0:g 0=0)(hm:M 0 0=0):flight S F A B v M w g 0=0:=by
 unfold flight
 rw [show envar (0:Lex F G X)= (0:Cellar X) from rfl,h0,bowl_center,central,hm,sub_zero,call,ContinuousLinearEquiv.map_zero]
 ext a; cases a<;>rfl

-- derivative for external socket
lemma tranquil (hg:Pace g)(j:Y)(i:Precision.Key F G) :
 Camera.wedge (.inl i) (fun t=> flight S F A B v M w g t (.inr j))=ᶠ[𝓝 0] (0:Still (Heights S F G X)):=by
 letI : DecidableEq (Heights S F G X) := Classical.decEq _
 let f:=fun x=>envar (I:=Precision.Key F G) (X:=X) x
 have ht:Tendsto f (𝓝 0) (𝓝 0):=smooth2.continuous.continuousAt.tendsto
 let R:Lex F G X→L[ℝ]Cellar X:= ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj (.inr i)
 have hdiff : ∀ᶠ x in 𝓝 0, DifferentiableAt ℝ g x :=
   (hg.eventually (by simp)).mono fun _ h => h.differentiableAt (by simp)
 filter_upwards [ht.eventually hdiff] with x hx
 let T:=ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Y=>ℝ) j
 have hp : (fun u : Lex F G X => flight S F A B v M w g u (.inr j)) = T ∘ (g ∘ R) := by
   funext u
   rfl
 rw [Camera.wedge, hp]
 change fderiv ℝ (T ∘ (g ∘ R)) x (Pi.single (.inl i) 1) = 0
 have hxR : DifferentiableAt ℝ g (R x) := hx
 have hcomp : DifferentiableAt ℝ (g ∘ R) x := hxR.comp _ R.differentiableAt
 rw [fderiv_comp _ T.differentiableAt hcomp,fderiv_comp _ hxR R.differentiableAt,R.fderiv, ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,show R (Pi.single (.inl i) 1)=0 from ?_, map_zero,map_zero]
 ext; simp [R]
end YM.RG08.Slate
