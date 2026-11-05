import YM.TraceExtension.Perfect.Lark
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}
lemma loom_read {Z : Peat G f} (h:Z∈loom G f): (ballX Z) 0=0 ∧ fderiv ℝ (ballX Z) 0=0 ∧ ContDiffAt ℝ ω (ballX Z) 0:=by
 obtain ⟨h,p⟩:= h; let A: Acr G f→L[ℝ] Link G f:= ContinuousLinearMap.fst _ _ _ ∘L (bite G f).toContinuousLinearMap
 have hp:ballX Z=(Z ∘ input G f) ∘ A:=rfl
 change braid _ _ 0 1 at p; have hx(p':ℕ)(he:p'≤1)(v) := DFunLike.congr_fun (wove (w:=A) (a:=0) ((map_zero A).symm ▸ p) ((map_zero A).symm ▸ (show ContDiffAt ℝ ω (Z ∘ input G f) 0 from (show Cleric Z from h).dye)) contDiffAt_const A.contDiff.contDiffAt p' he) v
 refine ⟨?_,?_,hp.symm ▸ ContDiffAt.comp _ ((map_zero A).symm ▸ (show Cleric Z from h).dye) A.contDiff.contDiffAt⟩
 · simpa only[hp,iteratedFDeriv_zero_apply,Function.comp_apply] using hx 0 (by norm_num) Fin.elim0
 ext1 u; have he := hx 1 le_rfl ![u]; rw [←hp] at he; rw [show ((fun _=> (0:ℝ)) ∘ A)=(fun _=>0) from rfl] at he; simp only [iteratedFDeriv_one_apply] at he; simpa using he
lemma loom_banks {Z:Peat G f} (h:Z∈loom G f) (u v:Acr G f): iteratedFDeriv ℝ 2 (ballX Z) 0 ![u,v]= iteratedFDeriv ℝ 2 (Z ∘ input G f) 0 ![(bite G f u).1,(bite G f v).1]:=by
 let A: Acr G f→L[ℝ] Link G f:= ContinuousLinearMap.fst _ _ _ ∘L (bite G f).toContinuousLinearMap; have hp:ballX Z=(Z ∘ input G f) ∘ A:=rfl
 obtain ⟨h,_⟩:= h; rw[hp,wired A ((map_zero A).symm ▸ ((show Cleric _ from h).dye.analyticAt)),map_zero]; congr 1; ext1 i; fin_cases i<;> rfl

def loom₂ (f:Side)(G:Gauge)(u v:Acr G f): (loom G f) →ₗ[ℝ] ℝ where
 toFun Z:=iteratedFDeriv ℝ 2 (ballX Z.val) 0 ![u,v]
 map_add' X Y:=by
    rw [show ballX (X+Y).val=ballX X.val+ballX Y.val from rfl,iteratedFDeriv_add_apply ((loom_read X.property).2.2.of_le le_top) ((loom_read Y.property).2.2.of_le le_top)]; rfl
 map_smul' c Y:=by rw[show ballX (c • Y).val=c • ballX Y.val from rfl,iteratedFDeriv_const_smul_apply]; rfl; exact (loom_read Y.property).2.2.of_le le_top

def dotB : Link G f→L[ℝ] Link G f→L[ℝ] ℝ:= ∑ i:Lines G f 1,(ContinuousLinearMap.smulRight (ContinuousLinearMap.proj i) (ContinuousLinearMap.proj i))
lemma fast_dot (x y:Link G f): dotB x y=x ⬝ᵥ y:=by rw [dotB,_root_.sum_apply,_root_.sum_apply];rfl
private abbrev left (G:Gauge)(f:Side): Acr G f→L[ℝ] Link G f:= ContinuousLinearMap.fst _ _ _ ∘L (bite G f).toContinuousLinearMap
private abbrev right (G:Gauge)(f:Side): Acr G f→L[ℝ] Link G f:= ContinuousLinearMap.snd _ _ _ ∘L (bite G f).toContinuousLinearMap
lemma rain_read {Y:Gal G f}(h:Y∈rains G f): (bottom Y) 0=0 ∧ fderiv ℝ (bottom Y) 0=0∧ContDiffAt ℝ ω (bottom Y) 0 ∧ ∀ u v : Acr G f,
   iteratedFDeriv ℝ 2 (bottom Y) 0 ![u,v]= (fderiv ℝ (Y ∘ input G f) 0 (bite G f u).1) ⬝ᵥ (bite G f v).2+(fderiv ℝ (Y ∘ input G f) 0 (bite G f v).1) ⬝ᵥ (bite G f u).2:=by
 obtain ⟨h,p⟩:= h; change Cloaked _ at h; change Y 1=0 at p
 let A:= left G f; let B:= right G f; let U: Acr G f→ Link G f:= (Y ∘ input G f) ∘ A; have hu:bottom Y=fun x=> dotB (U x) (B x):= funext fun x=> (fast_dot ..).symm
 rw[hu]; have ht:ContDiffAt ℝ ω U 0:= ContDiffAt.comp _ ((map_zero A).symm ▸ h.dye) A.contDiff.contDiffAt
 obtain ⟨hP,hv,H⟩:= criss dotB U (⇑B) ht B.contDiff.contDiffAt (by simp [U,p]) (map_zero B)
 refine ⟨hP,hv,((dotB (f:=f) (G:=G)).contDiff.contDiffAt.comp _ ht).clm_apply B.contDiff.contDiffAt,fun u v=>?_⟩
 have hx: fderiv ℝ U 0=(fderiv ℝ (Y ∘ input G f) 0) ∘L A:=by unfold U; rw[fderiv_comp 0 _ A.differentiableAt,map_zero,A.fderiv]; rw [map_zero]; exact h.dye.differentiableAt (by simp)
 rw [H,hx,B.fderiv,fast_dot,fast_dot];rfl

-- petal sign test
lemma capGauge_at (o:Site f)(a : Axis)(t:Tit G) (i:G.ColorIndex): (capGauge t o) (o,coord a,i)= if t.1=.watch then (if (coord a,i)=t.2 then 1 else 0) else 0:=by
 change ballad t o (.inr _) =_; unfold ballad; split
 next he=> change strollT t o _=_; unfold strollT; rw [he];rfl
 rfl
lemma dot_lush (u:Link G f)(x:Site f)(q:Axis)(v:Link G f): (petalPush x q v) ⬝ᵥ u= ∑ i:Axis,inner ℝ (petal x q i v) (edgeColor u (x,i)):=by
 unfold dotProduct; rw [Fintype.sum_prod_type,sum_eq_single x]; rotate_left
 · intro y _ hp; refine sum_eq_zero fun i _=>?_ ; rcases i with ⟨i,j⟩; rw [← edge_parts (petalPush x q v) (y,i) j,petalPush, ContinuousLinearEquiv.apply_symm_apply]; simp[edgeOf,hp]
 · simp
 rw [Fintype.sum_prod_type,← Equiv.sum_comp axisEquiv]; apply sum_congr rfl; intro i _
 rw[PiLp.inner_apply
 ]; refine sum_congr rfl fun k _=>?_
 rw [← edge_parts (petalPush x q v) (x,axisEquiv i) k,←edge_parts u (x,axisEquiv i) k,petalPush, ContinuousLinearEquiv.apply_symm_apply]; simp [edgeOf,mul_comm, show axisEquiv.symm (coord i)=i from axisEquiv.symm_apply_apply i]

def peakD (s:Tit G)(a:Axis):G.Color:= WithLp.toLp 2 fun i=>if s.1=.watch then (if (coord a,i)=s.2 then 1 else 0) else 0
lemma dot_watch (u: Link G f)(x:Site f)(q:Axis)(s:Tit G): (petalPush x q u) ⬝ᵥ (capGauge s x)=∑ i:Axis,inner ℝ (petal x q i u) (peakD s i):=by
 rw [dot_lush]; apply sum_congr rfl; intro i _; congr 1; ext k; rw [show (x,i)=edgeOf (x,axisEquiv i) from Prod.ext rfl (axisEquiv.symm_apply_apply i).symm,edge_parts]; exact capGauge_at x i s k

def missY (q:Axis)(s t:Tit G):= (∑ i:Axis,inner ℝ (mixB s 0 q i) (peakD t i))+(∑ i: Axis,inner ℝ (mixB t 0 q i) (peakD s i))
lemma miss_zero (a:Axis)(u v:Tit G)(h: ScoreG u + ScoreG v < 5): missY a u v=0:=by
 have hp(s t:Tit G)(h:ScoreG s+ScoreG t<5)(i:Axis): inner ℝ (mixB s 0 a i) (peakD t i)=0:=by
    by_cases H:t.1=.watch
    · have he:ScoreG t=3:=by simp [ScoreG,H,RowGrade.degree]
      rw [mix_void s (by omega), inner_zero_left]
    rw[show peakD t i=0 by ext k; unfold peakD; simp[H]]; simp
 unfold missY; simp only[hp u v h, hp v u (by omega),Finset.sum_const_zero, add_zero]
end YM.Trace.Perfect
