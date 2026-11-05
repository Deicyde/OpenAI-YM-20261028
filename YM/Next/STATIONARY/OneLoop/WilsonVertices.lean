import YM.Next.STATIONARY.Films.LeadingRay
import YM.Next.STATIONARY.OneLoop.Lattice

set_option autoImplicit false
/-!
# Plane Wilson ops. Compact identities for jets of the actual square.
Includes constants for cost to use before small-L. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {G : Gauge} {m : Side} {n : ℕ}
/- upsurge adapts the ordered-partition simplification in Mathlib's iteratedDerivWithin_vcomp_three to Wilson jets. Copyright (c) 2025 Yury Kudryashov. All rights reserved. Apache-2.0. See NOTICE. -/
section three
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma upsurge (f : Corn α → Corn β) (g : Corn β→ℝ) (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g (f 0)) (v x y : Phase α) : beat (g ∘ f) 0 3 ![v,x,y]= beat g (f 0) 3 ![cluster f 0 1 ![v],cluster f 0 1 ![x],cluster f 0 1 ![y]]+ (beat g (f 0) 2 ![cluster f 0 2 ![v,x],cluster f 0 1 ![y]] + beat g (f 0) 2 ![cluster f 0 1 ![x],cluster f 0 2 ![v,y]]) + (beat g (f 0) 2 ![cluster f 0 1 ![v],cluster f 0 2 ![x,y]] + beat g (f 0) 1 ![cluster f 0 3 ![v,x,y]]) := by
  let T : Fin 3→Phase α := ![v,x,y]
  rw [chain_eval f g 0 hf hg]
  simp only [← (OrderedFinpartition.extendEquiv 1).sum_comp,
    ← (OrderedFinpartition.extendEquiv 2).sum_comp, Fintype.sum_sigma,
    Fintype.sum_option, Nat.reduceAdd, OrderedFinpartition.extendEquiv_apply,
    OrderedFinpartition.extend_none, OrderedFinpartition.extend_some,
    OrderedFinpartition.extendMiddle_length, OrderedFinpartition.default_eq, Fintype.sum_unique,
    OrderedFinpartition.atomic_length, OrderedFinpartition.extendLeft_length, Fin.sum_univ_two]
  refine congr_arg₂ _ (congr_arg₂ _ (congr_arg _ ?_) (congr_arg₂ _ (congr_arg _ ?_) (congr_arg _ ?_))) (congr_arg₂ _ (congr_arg _ ?_) (congr_arg _ ?_))
  all_goals funext i; fin_cases i <;> apply congr_arg (⇑(cluster f 0 _)) <;> ext1 k
  all_goals fin_cases k <;> rfl
end three
end YM.Stationary
end

/-!
# Hessian of an orbit commutator -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {p : Clip} {X A : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedRing A] [NormedAlgebra ℝ A]

variable [CompleteSpace A]
lemma furtiveP (f g : X→A) (a : X) (h : DifferentiableAt ℝ f a) (he : DifferentiableAt ℝ g a) (p) : fderiv ℝ (f*g) a p= f a * fderiv ℝ g a p+ fderiv ℝ f a p * g a := by rw [fderiv_mul' h he]; rfl
lemma furtive (f g : X→A) (h : AnalyticAt ℝ f 0) (he : AnalyticAt ℝ g 0) (p q) : iteratedFDeriv ℝ 2 (f*g) 0 ![p,q] = f 0*iteratedFDeriv ℝ 2 g 0 ![p,q] + fderiv ℝ f 0 p*fderiv ℝ g 0 q+ (fderiv ℝ f 0 q*fderiv ℝ g 0 p+ iteratedFDeriv ℝ 2 f 0 ![p,q] * g 0) := by
  let V (U : X→A) (z : X) := fderiv ℝ U z q
  have hv (F : X→ A) (hf : AnalyticAt ℝ F 0) : fderiv ℝ (V F) 0 p = iteratedFDeriv ℝ 2 F 0 ![p,q] := by
    have hh := prodT (n:=1) ![p] q F 0 hf.contDiffAt
    rw [iteratedFDeriv_one_apply,show (Fin.snoc (![p]:Fin 1 → _) q)= ![p,q] by ext1 i; fin_cases i <;> rfl] at hh; exact hh
  have hp (f : X→A) (h : AnalyticAt ℝ f 0) : DifferentiableAt ℝ (V f) 0 := ((h.contDiffAt (n:=ω)).fderiv_right (m:=ω) (by simp)).differentiableAt (by simp) |>.clm_apply (differentiableAt_const _)
  have ht : V (f*g) =ᶠ[𝓝 0] f * V g + V f*g := by
    filter_upwards [h.eventually_analyticAt, he.eventually_analyticAt] with x hx hb
    exact furtiveP _ _ _ hx.differentiableAt hb.differentiableAt _
  rw [← hv _ (h.mul he), ht.fderiv_eq, fderiv_add (h.differentiableAt.mul (hp g he)) ((hp f h).mul he.differentiableAt),_root_.add_apply, furtiveP _ _ 0 h.differentiableAt (hp g he), furtiveP _ _ 0 (hp f h) he.differentiableAt, hv f h, hv g he]

lemma spark_stone (V F E : X→A) (hp : AnalyticAt ℝ V 0) (hf : AnalyticAt ℝ F 0) (hh : AnalyticAt ℝ E 0) (h : F 0=1) (he : E 0=1) (hF : V 0=1) :
    let H := (F*E-E*F)*V+1
    AnalyticAt ℝ H 0 ∧ H 0=1 ∧ fderiv ℝ H 0=0 ∧ ∀ p q, iteratedFDeriv ℝ 2 H 0 ![p,q]= ((fderiv ℝ F 0 p)*(fderiv ℝ E 0 q)-(fderiv ℝ E 0 q)*(fderiv ℝ F 0 p)) + ((fderiv ℝ F 0 q)*(fderiv ℝ E 0 p)-(fderiv ℝ E 0 p)*(fderiv ℝ F 0 q)) := by
  intro H
  let B := F*E-E*F
  have h0 : B 0=0 := by simp [B,h,he]
  have hK : fderiv ℝ B 0=0 := by
    apply ContinuousLinearMap.ext; intro x; unfold B
    rw [fderiv_sub (hf.mul hh|>.differentiableAt) (hh.mul hf|>.differentiableAt), _root_.sub_apply,furtiveP _ _ _ hf.differentiableAt hh.differentiableAt,furtiveP _ _ _ hh.differentiableAt hf.differentiableAt,h,he]; simp [add_comm]
  have hb : AnalyticAt ℝ (B*V) 0 := ((hf.mul hh).sub (hh.mul hf)).mul hp
  have hu : AnalyticAt ℝ (1:X→A) 0 := analyticAt_const
  refine ⟨(hb.add hu),by unfold H; simp [h,he],?_,?_⟩
  · apply ContinuousLinearMap.ext; intro x; unfold H
    change fderiv ℝ (B*V+1) 0 x=_
    rw [fderiv_add hb.differentiableAt hu.differentiableAt,_root_.add_apply,furtiveP B _ _ ((hf.mul hh|>.sub (hh.mul hf)).differentiableAt) hp.differentiableAt,h0,hK,show fderiv ℝ (1:X→A) 0=0 from (hasFDerivAt_const 1 _).fderiv]; simp
  intro p q; change iteratedFDeriv ℝ 2 (B*V+1) _ _=_
  rw [iteratedFDeriv_add_apply hb.contDiffAt hu.contDiffAt,_root_.add_apply, furtive B V ((hf.mul hh).sub (hh.mul hf)) hp,h0,hK,hF, show iteratedFDeriv ℝ 2 (1:X→A) 0=0 from congr_fun (iteratedFDeriv_const_of_ne (by decide) 1) (0:X)]
  simp only [_root_.zero_apply,zero_mul,zero_add,mul_one,add_zero]; unfold B
  rw [iteratedFDeriv_sub_apply (hf.mul hh|>.contDiffAt) (hh.mul hf|>.contDiffAt),_root_.sub_apply, furtive F E hf hh,furtive E F hh hf,h,he]; simp only [mul_one,one_mul]; abel

variable {T W : X → G.El}
def jointly (t w : G.El) := t*w*t⁻¹*w⁻¹
-- Taylor of commutator at unit matrix
lemma echo_mat (h : T 0=1) (he : W 0=1) (hf : AnalyticAt ℝ (G.mat ∘ T) 0) (hh : AnalyticAt ℝ (G.mat ∘ W) 0) :
    let F := G.mat ∘ T; let E := G.mat ∘ W; let H x := G.mat (jointly (T x) (W x)); AnalyticAt ℝ H 0 ∧ H 0=1 ∧ fderiv ℝ H 0=0 ∧ ∀ p q, iteratedFDeriv ℝ 2 H 0 ![p,q]= ((fderiv ℝ F 0 p)*(fderiv ℝ E 0 q)-(fderiv ℝ E 0 q)*(fderiv ℝ F 0 p)) + ((fderiv ℝ F 0 q)*(fderiv ℝ E 0 p)-(fderiv ℝ E 0 p)*(fderiv ℝ F 0 q)) := by
  intro F E H; let u : X→G.Mat := fun _=>1
  let B := F*E-E*F
  let V x := G.mat ((T x)⁻¹)*G.mat ((W x)⁻¹)
  have ht : H=B*V+u := by
    ext1 i; change G.mat (jointly (T i) (W i))=(G.mat (T i)*G.mat (W i)-G.mat (W i)*G.mat (T i)) * (G.mat ((T i)⁻¹)*G.mat ((W i)⁻¹)) +1
    rw [Matrix.sub_mul, ← G.mat_mul, ← G.mat_mul, ← G.mat_mul, ← G.mat_mul, ← G.mat_mul,show W i*T i*((T i)⁻¹*(W i)⁻¹)=1 by group,G.mat_one, sub_add_cancel]; unfold jointly; rw [mul_assoc (T i*W i)]
  have hF : F 0=1 := by simp [F,h];
  have hE : E 0=1 := by simp [E,he]
  have h0 : H 0=1 := by simp [H,jointly,h,he]

  have hp : AnalyticAt ℝ V 0 := by
    let z : G.Mat≃L[ℝ] G.Mat := starL ℝ
    unfold V; simp only [G.mat_inv]; exact AnalyticAt.mul (z.contDiff.contDiffAt.comp (f:=F) _ hf.contDiffAt|>.analyticAt) ((z.contDiff.contDiffAt.comp (f:=E) _ hh.contDiffAt).analyticAt)
  rw [ht]
  exact spark_stone V F E hp hf hh hF hE (by simp [V,h,he])
lemma echo_clr (x : G.Color) : fderiv ℝ G.plog 1 (G.colorMat x)=x := by
  let F (b : ℝ) := G.lieExp (b • x)
  have hz : F (0:ℝ)=1 := by simp [F]
  have ht : HasFDerivAt G.plog (fderiv ℝ G.plog 1) (G.mat (F (0:ℝ))) := by erw [hz,G.mat_one]; exact G.plog_diff.differentiableAt (by simp)|>.hasFDerivAt
  exact (ht.comp_hasDerivAt 0 (exp_ray x)).unique (ray_recall hz (exp_ray x))
lemma echo_power (h : T 0=1) (he : W 0=1) (hf : AnalyticAt ℝ (G.mat ∘ T) 0) (hh : AnalyticAt ℝ (G.mat ∘ W) 0)
    {v w : X → G.Color} (hv : ∀ p,fderiv ℝ (G.mat ∘ T) 0 p=G.colorMat (v p)) (hw : ∀ p,fderiv ℝ (G.mat ∘ W) 0 p=G.colorMat (w p)) (x y) : iteratedFDeriv ℝ 2 (fun x=> plogC G (jointly (T x) (W x))) 0 ![x,y]= G.ad (v x) (w y)+G.ad (v y) (w x) := by
  let H x := G.mat (jointly (T x) (W x)); change iteratedFDeriv ℝ 2 (G.plog ∘ H) 0 ![x,y]=_
  obtain ⟨hL,h1,h2,h3⟩ := echo_mat h he hf hh
  have hK (x y) : iteratedFDeriv ℝ 2 H 0 ![x,y]= _ := h3 x y
  erw [pay_second _ (show ContDiffAt ℝ ω H 0 from hL.contDiffAt),show H 0=1 from h1,show fderiv ℝ H 0=0 from h2,hK, hv,hv,hw,hw,← Gauge.colorMat_ad,← Gauge.colorMat_ad,← map_add,echo_clr]; pick_goal 2
  · erw [show H 0=1 from h1]; exact G.plog_diff
  simp [iteratedFDeriv_two_apply]
  change fderiv ℝ (fderiv ℝ G.plog) 1 0 0=0
  simp
end YM.Stationary
end

/-!
# The plaq logarithm as scalar orbit potential. First order stencil for two
chart blocks (potential and left-vector perturbation). Record volumes preserved.
 -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {p : Clip} {α : Type} [Fintype α] {m : Side}

section
variable (G)
abbrev Gem := Fin 4×Bool×G.ColorIndex
def deter (u : Bool) (i : Fin 4) : Corn (Gem G)→L[ℝ] G.Color :=
    (WithLp.linearEquiv 2 ℝ (Corn G.ColorIndex)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (i,u,j))

def spree (i : Fin 4) : Corn (Gem G) →L[ℝ] G.Color := deter G true i + deter G false i
def pious (i : Fin 4) (x : Corn (Gem G)) := G.lieExp (deter G true i x)*G.lieExp (deter G false i x)
def pliant (x : Corn (Gem G)) := pious G 0 x*pious G 1 x*(pious G 2 x)⁻¹*(pious G 3 x)⁻¹
variable {G}
lemma gemat0 (i : Fin 4) : pious G i 0=1 := by simp [pious]
@[simp] lemma pliant0 : pliant G 0=1 := by simp [pliant,gemat0]
lemma gemDiff (i : Fin 4) : AnalyticAt ℝ (G.mat ∘ pious G i) 0 := by
  simp only [Function.comp_def,pious,G.mat_mul]
  let U (u : Bool) := fun x => G.mat (G.lieExp (deter G u i x))
  have he u : AnalyticAt ℝ (U u) 0 := (G.exp_jet.comp (f:=deter G u i) (deter G u i).contDiff).contDiffAt.analyticAt
  exact (he true).mul (he false)
lemma piecePitch (i : Fin 4) (x : Corn (Gem G)) : HasDerivAt (fun t : ℝ => G.mat (pious G i (t • x))) (G.colorMat (spree G i x)) 0 := by
  let T := deter G true i; let W := deter G false i
  simp only [pious,G.mat_mul,map_smul]
  convert! (exp_ray (T x)).mul (exp_ray (W x)) using 1
  change _=G.colorMat _ * _ + _*G.colorMat _
  simp only [zero_smul,G.mat_lieExp_zero,G.mat_one,mul_one,one_mul]; rw [spree]; simp [T,W]

lemma pliantDiff : AnalyticAt ℝ (G.mat ∘ pliant G) 0 := by
  let z : G.Mat≃L[ℝ] G.Mat := starL ℝ
  have hx i := gemDiff (G:=G) i
  have he i : AnalyticAt ℝ (fun x=> star (G.mat (pious G i x))) 0 := (z.contDiff.contDiffAt.comp (f:=G.mat∘pious G i) _ (hx i).contDiffAt).analyticAt
  simp only [Function.comp_def,pliant,G.mat_mul,G.mat_inv]
  exact (((hx 0).mul (hx 1)).mul (he 2)).mul (he 3)
lemma pliant_ray (x : Corn (Gem G)) : HasDerivAt (fun t : ℝ => G.mat (pliant G (t • x))) (G.colorMat (spree G 0 x+spree G 1 x -spree G 2 x - spree G 3 x)) 0 := by
  have hx i := piecePitch i x
  simp only [pliant,G.mat_mul,G.mat_inv]; convert! (((hx 0).mul (hx 1)).mul (hx 2).star).mul (hx 3).star using 1
  simp only [zero_smul,gemat0, G.mat_one,G.colorMat_skew,mul_one,one_mul, map_add,map_sub,Pi.mul_apply,star_one]
  abel

abbrev Lilts (G : Gauge) : G.Color ≃L[ℝ] Corn G.ColorIndex := (WithLp.linearEquiv 2 ℝ _).toContinuousLinearEquiv

def peridot (x : Corn (Gem G)) := Lilts G (plogC G (pliant G x))
def pricePow (G : Gauge) (x : Corn G.ColorIndex) := G.price (G.lieExp ((Lilts G).symm x))
lemma peridot0 (G : Gauge) : peridot (0:Corn (Gem G))=0 := by simp [peridot]
lemma peridot_green : AnalyticAt ℝ (peridot (G:=G)) 0 := by
  apply ContDiffAt.analyticAt; refine (Lilts G).contDiff.contDiffAt.comp (f:=G.plog ∘ (G.mat ∘ pliant G)) _ ?_; exact (show ContDiffAt ℝ ω G.plog ((G.mat∘pliant G) 0) by simp only [Function.comp_apply, pliant0,G.mat_one]; exact G.plog_diff).comp (f:=G.mat∘pliant G) _ pliantDiff.contDiffAt
lemma peridot_live : AnalyticAt ℝ (pricePow G) 0 :=
    matrix_price_jet ((G.exp_jet.comp (Lilts G).symm.contDiff).contDiffAt) |>.analyticAt
lemma peridot_call : pricePow G ∘ peridot =ᶠ[𝓝 0] G.price ∘ pliant G := by
  have he i : Continuous (pious G i) := by unfold pious; fun_prop
  have hx : Continuous (pliant G) := by unfold pliant; fun_prop
  filter_upwards [(show Tendsto (pliant G) (𝓝 0) (𝓝 1) from pliant0 ▸ hx.continuousAt.tendsto).eventually G.plog_right] with x hx
  unfold pricePow peridot; simp only [Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply]; rw [show G.lieExp (plogC G _) = _ from hx]
lemma peridot_fder (x : Corn (Gem G)) : fderiv ℝ peridot 0 x = Lilts G (spree G 0 x + spree G 1 x - spree G 2 x-spree G 3 x) := by
  refine HasDerivAt.unique (Push.side _ peridot_green.differentiableAt x) ?_
  exact (Lilts G).hasFDerivAt.comp_hasDerivAt 0 (ray_recall (u:=fun a:ℝ=>pliant G (a • x)) (by simp) (pliant_ray x))
lemma pricePow_h : fderiv ℝ (pricePow G) 0=0 ∧ ∀ x y : Corn G.ColorIndex, iteratedFDeriv ℝ 2 (pricePow G) 0 ![x,y] = dotProduct x y := by
  refine (Work.F03.hessian_of_limit (f:=pricePow G) peridot_live.contDiffAt (Q:=dotProduct) (fun x=> ?_) add_dotProduct dotProduct_comm).2
  let z := (Lilts G).symm x
  rw [show dotProduct x x=‖z‖^2 by rw [← real_inner_self_eq_norm_sq, Work.F03.inner_color]; rfl]
  unfold pricePow; simp only [map_smul]
  exact Work.F03.price_limit (V:=fun t : ℝ=> G.lieExp (t • z)) (by simp) (exp_ray z)

-- stencil consultations.
def tenderPhi (a : PlaqAxes) : Fin 4 → Axis := ![a.val.1,a.val.2,a.val.1,a.val.2]
def tenderOf (a : PlaqAxes) : Fin 4 → Cover := ![0,step a.val.1,step a.val.2,0]

def tenderR (a : PlaqAxes) (p : Site m) (G : Gauge) (R : Type) [CommRing R] : (Co m (Crisp G)→R) →ₗ[R] (Gem G →R) := LinearMap.pi fun i=> LinearMap.proj (p+wrap _ (tenderOf a i.1),i.2.1,coord (tenderPhi a i.1),i.2.2)

def shineF (x : Corn (Co m (Crisp G))) := input G m (wheat true x) * input G m (wheat false x)
lemma shinelet (x : Corn (Co m (Crisp G))) (i : Fin 4) (y : Site m) (a : PlaqAxes) : shineF x (y+wrap _ (tenderOf a i), tenderPhi a i)=pious G i (tenderR a y G ℝ x) := by
  unfold shineF; rw [Pi.mul_apply,encode_link,encode_link]; rfl
lemma shineworks (x : Corn (Co m (Crisp G))) (y : Site m) (a : PlaqAxes) : faceValue (shineF x) (y,a)=pliant G (tenderR a y G ℝ x) := by
  unfold faceValue travel square; let U:=shineF x
  unfold pliant; simp only [← shinelet, travel,Step.vec_pos,Step.vec_neg,Step.neg_read,Step.pos_read,tenderPhi,tenderOf,map_zero,wrap_step,Matrix.cons_val_zero,Matrix.cons_val_one, mul_one,add_zero]
  simp [mul_assoc]; rw [add_right_comm y]; simp [add_assoc,sub_eq_add_neg]
lemma dough_shine : (fun x : Corn (Co m (Crisp G))=> input G m (dough G m x)) =ᶠ[𝓝 0] shineF := by
  let M (b : Bool) : Corn (Co m (Crisp G))→L[ℝ] Link G m := (wheat b).toContinuousLinearMap
  have hx : shineF (0:Corn (Co m (Crisp G)))=1 := by unfold shineF; simp
  have hh : Continuous (shineF (G:=G) (m:=m)) := Continuous.mul (input_cont.comp (M true).continuous) (input_cont.comp (M false).continuous)
  exact (show Tendsto (shineF (G:=G) (m:=m)) (𝓝 0) (𝓝 1) by rw [← hx]; exact hh.tendsto 0).eventually content_encodes
end
end YM.Stationary
end

/-!
# Wilson chart identification at physical test. Includes first background
p at nominal direction b (peridot used also for its tangent shift). -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {p : Clip} {V : Jar G} {m : Side} {n : ℕ} {σ C : ℝ}

def binderW (p : Face (Per m)) (x : Corn (Co m (Crisp G))) := (pricePow G ∘ peridot) (tenderR p.2 p.1 G ℝ x)
lemma binder_green (p : Face (Per m)) : AnalyticAt ℝ (binderW (G:=G) p) 0 := by
  let L := (tenderR p.2 p.1 G ℝ).toContinuousLinearMap; have hh : AnalyticAt ℝ (pricePow G ∘ peridot) 0 := AnalyticAt.comp (f:=peridot) (by rw [peridot0]; exact peridot_live) peridot_green
  exact AnalyticAt.comp (g:=pricePow G ∘ peridot) (f:=L) (by rw [map_zero]; exact hh) (L.analyticAt _)
lemma binder_cover : WilsonQ G m ∘ (dough G m)=ᶠ[𝓝 0] (fun x=> ∑ y,binderW y x) := by
  have he (i : Face (Per m)) : binderW (G:=G) i=ᶠ[𝓝 0] fun x=>G.price (faceValue (shineF x) i) := by
    let L := (tenderR i.2 i.1 G ℝ).toContinuousLinearMap
    filter_upwards [(show Tendsto L (𝓝 0) (𝓝 0) by simpa using L.continuous.tendsto 0).eventually peridot_call] with x hx
    rw [← show (i.1,i.2)= i from rfl, shineworks]; exact hx
  filter_upwards [eventually_all.mpr he,dough_shine] with x hx hQ
  change Wilson.energy (input _ _ (dough G m x))=_
  rw [show input _ _ _=shineF x from hQ]
  exact sum_congr rfl fun i _=> (hx i).symm
-- corner packet colors Complex basis only. κ.
def streamS (a : PlaqAxes) (b : Fslot G) (p : Momentum) (w : Bool) (i : Gem G) := if i.2.1=w then mode p (tenderOf a i.1) * (Pi.single b 1 : Phase (Fslot G)) (coord (tenderPhi a i.1),i.2.2) else 0
lemma streamed (x y : Site m) (a : PlaqAxes) (b : Fslot G) (p : Momentum) (h : rolls (mon y) p) (w : Bool) : tenderR a x G ℂ (sprout w (relay y b))=cell y x • streamS a b p w := by
  ext1 i; rcases i with ⟨i,j,l⟩; by_cases he : j=w
  · simp [tenderR, sprout, relay,tune,he,mul_assoc,streamS,h.exp]
  simp [tenderR,sprout,he,streamS]
-- Taylor form. z,p ordering

def cornell (b x y : Fslot G) (p k : Momentum) (a : PlaqAxes) := beat (pricePow G ∘ peridot) 0 3 ![streamS a b p false,streamS a x (-(k+p)) true,streamS a y k true]
def perigee (b x y : Fslot G) (p k : Momentum) := ∑ a : PlaqAxes, cornell b x y p k a
lemma granite_identifies (b x y : Fslot G) (u v w : Site m) (p k : Momentum) (h : rolls (mon u) p) (hp : rolls (mon w) k) (he : u+v+w=0) : liquid (creme 1) (WilsonQ G m) ![relay u b,relay v x,relay w y] = (cents m:ℂ)*perigee b x y p k := by
  let i := sprout false (relay u b); let j := sprout true (relay v x); let l := sprout true (relay w y)
  have ht : rolls (mon v) (-(k+p)) := by
    rw [eq_neg_of_add_eq_zero_left (show v+(w+u)=0 from (show v+(w+u)=u+v+w by abel).trans he)]; exact (hp.combine h).flip_sign
  have hh : beat (WilsonQ G m ∘ dough G m) 0 3=beat (fun x=>∑ y:Face (Per m),binderW y x) 0 3 := by simp only [beat,(binder_cover (m:=m) (G:=G) |>.iteratedFDeriv ℝ 3).eq_of_nhds]
  have hj (a : Face (Per m)) : beat (binderW a) 0 3 ![i,j,l]=cornell b x y p k a.2 := by
    let L := tenderR a.2 a.1 G ℂ
    have hv : AnalyticAt ℝ (pricePow G ∘ peridot) 0 := AnalyticAt.comp (g:=pricePow G) (f:=peridot) (by rw [peridot0]; exact peridot_live) peridot_green
    rw [show binderW a=(pricePow G∘peridot)∘(tenderR a.2 a.1 G ℝ).toContinuousLinearMap from rfl,evaluated L (fun x=>rfl) hv,MultilinearMap.compLinearMap_apply]
    let Q : Fin 3→ ℂ := ![cell u a.1,cell v a.1,cell w a.1]
    let y' := ![streamS a.2 b p false,streamS a.2 x (-(k+p)) true,streamS a.2 y k true]
    rw [show (fun k=> L ((![i,j,l]:Fin 3→ _) k))=fun k=> Q k • y' k by
      funext k; fin_cases k; exacts [streamed a.1 u a.2 b p h false,streamed a.1 v a.2 x _ ht true,streamed a.1 w a.2 y _ hp true],MultilinearMap.map_smul_univ]
    have hy : ∏ i,Q i=1 := by
      unfold Q; rw [Fin.prod_univ_succ,Fin.prod_univ_succ,Fin.prod_univ_one]; simp only [Matrix.cons_val_zero]; change cell u a.1*(cell v a.1*cell w a.1)=_
      rw [cell_duality u a.1,cell_duality v a.1,cell_duality w a.1,← cell_add,← cell_add,← add_assoc,he]; simp
    rw [hy,one_smul]; rfl
  rw [liquid,MultilinearMap.compLinearMap_apply,hh, show (fun k:Fin 3=> sprout (m:=m) (creme 1 k) ((![relay u b,relay v x,relay w y]:Fin 3 →Phase (Lines G m 1)) k))=![i,j,l] by ext1 a; fin_cases a <;> rfl, beat_summations univ _ (fun i _=> (binder_green i).contDiffAt)]
  simp_rw [hj]; rw [Fintype.sum_prod_type]; simp [perigee,cents]
lemma vintage_knows (h : V.grey) (hx : V.fees σ C) (i j l : Fslot G) (u w : Site m) (p k) (hu : rolls (mon u) p) (hw : rolls (mon w) k) : V.cast.spot i p k j l=perigee i j l p k := by
  let v := -(w+u)
  have hv : rolls (mon v) (-(k+p)) := (hw.combine hu).flip_sign
  have he : u+v+w=0 := by unfold v; abel
  have hr : ∑ i, (![u,v,w]: Fin 3→Site m) i=0 := by simp [Fin.sum_univ_succ, ← add_assoc,he]
  have ht := drinkLocate (![i,j,l]:Breed 2 (Loc G 1)) (![u,v,w]) (![p,-(k+p),k]) (fun a=> by fin_cases a; exacts [hu,hv,hw]) (h _).2.1 hx.2.1
  rw [if_pos hr, show (fun a=>relay ((![u,v,w]:Fin (2+1)→_) a) ((![i,j,l]:Breed 2 _) a))=![relay u i,relay v j,relay w l] by
    ext1 x; fin_cases x <;> rfl, granite_identifies i j l u v w p k hu hw he] at ht
  change _ = perigee _ _ _ _ _; apply mul_left_cancel₀ (show (cents m:ℂ)≠0 by exact_mod_cast cents_pos.ne')
  rw [ht]; unfold cents; push_cast; apply congr_arg _
  change chaperon _ _ _=chaperon _ _ _
  rw [show duoTop 1 (![i]) j l= ![i,j,l] by ext1 a; fin_cases a <;> rfl]
  rw [show wineShift (![p] : Fin 1→Momentum) k= ![p,-(k+p),k] by
    unfold wineShift; rw [Fin.sum_univ_one]; ext1 a; fin_cases a <;> rfl]
-- now pass to dense p,k. use cofinal ANY.
lemma stream_diff (b : Fslot G) (a : PlaqAxes) (c : Bool) : ContDiff ℂ ω (fun p : Momentum => streamS a b p c) := by
  refine contDiff_pi.mpr (fun i => ?_); unfold streamS; split; next e => unfold Laurent.mode; fun_prop
  exact contDiff_const
lemma perigee_hold (b x y : Fslot G) : Continuous (fun z : Momentum × Momentum => perigee b x y z.1 z.2) := by
  unfold perigee; refine continuous_finsetSum univ (fun a _ => ?_)
  let v := fun z : Momentum× Momentum=> (![streamS a b z.1 false,streamS a x (-(z.2+z.1)) true,streamS a y z.2 true]:Fin 3→Phase (Gem G))
  have h : Continuous v := continuous_pi fun i=> by
    fin_cases i; exacts [(stream_diff b a false).continuous.comp continuous_fst,(stream_diff x a true).continuous.comp ((continuous_snd.add continuous_fst).neg),(stream_diff y a true).continuous.comp continuous_snd]
  exact (listen _).cont.comp h
lemma steady_grid (L Y : Momentum →Momentum →ℂ) (p k : Momentum) (hp : star p=p) (hk : star k=k)
    (hl : ContinuousAt (uncurry L) (p,k)) (hY : ContinuousAt (uncurry Y) (p,k))
    (he : ∀ m : Side, ∀ u v : Site m,∀ p k,rolls (mon u) p→ rolls (mon v) k→ L p k=Y p k) : L p k=Y p k := by
  obtain ⟨u,P,ht,hP⟩ := mesh_stride walent walentes p hp
  obtain ⟨v,T,hK,hT⟩ := mesh_stride walent walentes k hk
  have hL : Tendsto (fun i => (P i,T i)) atTop (𝓝 (p,k)) := ht.prodMk_nhds hK
  have hy : uncurry L ∘ (fun i => (P i,T i))=ᶠ[atTop] uncurry Y ∘ (fun i => (P i,T i)) :=
    Eventually.of_forall fun i=> he (walent i) (u i) (v i) _ _ (hP i) (hT i)
  exact tendsto_nhds_unique_of_eventuallyEq (hl.tendsto.comp hL) (hY.tendsto.comp hL) hy
lemma vintage_sings (h : V.grey) (hx : V.fees σ C) (hs : 0<σ) (b x y : Fslot G) (p k : Momentum) (hp : star p=p) (hk : star k=k) : V.cast.spot b p k x y=perigee b x y p k := by
  have hh : Avenue σ p k := ⟨Work.F07.realStrip _ hs hp, Work.F07.realStrip _ hs hk, Work.F07.realStrip _ hs (by rw [star_add,hp,hk])⟩
  refine steady_grid (fun p k => V.cast.spot b p k x y) (perigee b x y) p k hp hk ?_ ((perigee_hold b x y).continuousAt (x:=(p,k))) (fun m u v p k hp hk => vintage_knows h hx b x y u v p k hp hk)
  exact ((hx.live.spot b).shape hh x y).continuousAt
end YM.Stationary
end

/-!
# Leading Wilson components. Real-axis derivatives unnormalized. Projection
rotates color only. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius ComplexConjugate
variable {G : Gauge} {P : Patch} {V : Jar G} {m : Side} {σ C : ℝ}

section content
-- Real unit basis. Choice via WithLp
abbrev pearl (i : G.ColorIndex) := (Lilts G).symm (Pi.single i 1)
def slatV (b : Fslot G) (i : Axis) : G.Color := if coord i=b.1 then pearl b.2 else 0
def scatterRun (w : Bool) (a : PlaqAxes) (b : Fslot G) (i : Gem G) := if i.2.1=w then ((Lilts G) (slatV b (tenderPhi a i.1))) i.2.2 else 0
lemma lightFront (b : Fslot G) (i : Axis) (l : G.ColorIndex) : (Pi.single b 1 : Phase (Fslot G)) (coord i,l)=((Lilts G) (slatV b i) l:ℂ) := by
  rcases b with ⟨b,h⟩; unfold slatV; split <;> rename_i he
  · simp only [(Lilts G).apply_symm_apply]; dsimp only at *; rw [he]; by_cases hv : l=h <;> simp [Pi.single_apply, *]
  dsimp only at *; simp [Pi.single_apply, *]
lemma deter_at (w : Bool) (a : PlaqAxes) (b : Fslot G) (u : Bool) (i : Fin 4) : deter G u i (scatterRun w a b)=if u=w then slatV b (tenderPhi a i) else 0 := by
  apply (Lilts G).injective; funext k
  change scatterRun w a b (i,u,k)= _; unfold scatterRun; split <;> rfl
lemma scatterSpree (w : Bool) (a : PlaqAxes) (b : Fslot G) (i) : spree G i (scatterRun w a b)=slatV b (tenderPhi a i) := by unfold spree; erw [_root_.add_apply]; rw [deter_at,deter_at]; cases w <;> simp
lemma pearlPitch (w : Bool) (a : PlaqAxes) (b : Fslot G) (p : Momentum) (i : Gem G) : streamS a b p w i= mode p (tenderOf a i.1)* scatterRun w a b i := by
  unfold streamS scatterRun; split <;> simp [*,lightFront _ _ _]
lemma scatterTrace (w : Bool) (a : PlaqAxes) (b : Fslot G) : streamS a b 0 w=axes (scatterRun w a b) := funext fun i=> by simp [pearlPitch]; rfl

-- arbitrary repeated period. project all 4 legs onto 0,1 for stories

def reinsF (G : Gauge) : Corn (Gem G)→L[ℝ] Corn (Gem G) := ContinuousLinearMap.pi fun i:Gem G=> ContinuousLinearMap.proj ((![0,1,0,1] : Fin 4 → Fin 4) i.1,i.2)
lemma reinsStay (w : Bool) (a : PlaqAxes) (b : Fslot G) : reinsF G (scatterRun w a b)=scatterRun w a b := by ext1 i; rcases i with ⟨i,j⟩; fin_cases i <;> rfl
lemma reinsPious (x : Corn (Gem G)) : pliant G (reinsF G x) = jointly (pious G 0 x) (pious G 1 x) := rfl
lemma peridot_twirl (x y : Corn (Gem G)) (h : reinsF G x=x) (he : reinsF G y=y) :
    iteratedFDeriv ℝ 2 peridot 0 ![x,y]= Lilts G (G.ad (spree G 0 x) (spree G 1 y)+ G.ad (spree G 0 y) (spree G 1 x)) := by
  let T := reinsF G; let δ z := plogC G (pliant G z); let J := (Lilts G).toContinuousLinearMap
  let M z := plogC G (jointly (pious G 0 z) (pious G 1 z))
  have ht : M=δ ∘ T := rfl
  have hx i u : fderiv ℝ (G.mat ∘ pious G i) 0 u=G.colorMat (spree G i u) := (Push.side _ (gemDiff i).differentiableAt u).unique (piecePitch i u)
  have hp := echo_power (gemat0 _) (gemat0 _) (gemDiff 0) (gemDiff 1) (v:=spree G 0) (w:=spree G 1) (hx 0) (hx 1) x y
  have hb : AnalyticAt ℝ M 0 := by
    rw [ht]; apply AnalyticAt.comp (g:=δ) (f:=T) _ (T.analyticAt _)
    rw [map_zero]; exact AnalyticAt.comp (f:=peridot) ((Lilts G).symm.analyticAt _) peridot_green
  have ho : T ∘ (![x,y]:Fin 2→_)=![x,y] := by ext1 i; fin_cases i; exact h; exact he
  have hv := wired T (f:=peridot) (by rw [map_zero]; exact peridot_green (G:=G)) 2 ![x,y]
  rw [ho,map_zero] at hv
  rw [← hv,show peridot ∘ (T)=J ∘ M from rfl]; exact (DFunLike.congr_fun (J.iteratedFDeriv_comp_left hb.contDiffAt (by exact (show (↑(2:ℕ) : WithTop ℕ∞)≤ω from le_top))) ![x,y]).trans (congr_arg (fun x => J x) hp)

-- second insertion pair at static; antisymmetric in slots if reverse has sign.
def gemstone (a : PlaqAxes) (b c : Fslot G) := Lilts G (G.ad (slatV b a.val.1) (slatV c a.val.2) + G.ad (slatV c a.val.1) (slatV b a.val.2))
lemma curlGem (a : PlaqAxes) (b c : Fslot G) (u w : Bool) : cluster peridot 0 2 ![streamS a b 0 u,streamS a c 0 w]=axes (gemstone a b c) := by
  let x := scatterRun u a b; let y := scatterRun w a c; rw [scatterTrace,scatterTrace]
  rw [show ![axes x,axes y]=axes ∘ (![x,y]:Fin 2 → _) by funext i; fin_cases i <;> rfl,line_real _ _ _ peridot_green,peridot_twirl x y (reinsStay ..) (reinsStay ..)]; unfold x y; simp_rw [scatterSpree]; rfl
end content
end YM.Stationary
end

/-!
# First plaq beat obtains literal precision. Rays specialized later on
 momentum budget. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius ComplexConjugate
variable {G : Gauge} {P : Patch} {p : Clip} {V : Jar G} {m : Side}

section curls
lemma Leads.luster (j) : Leads (fun p=> cluster (peridot (G:=G)) 0 1 ![p] j) := by
  intro u v; dsimp only
  simp_rw [band_line]
  have ht (p : Phase (Gem G)) : (![p]:Fin 1→_)=update (0:Fin 1→Phase (Gem G)) 0 p := by funext i; fin_cases i; simp
  rw [ht (axes u+Complex.I • axes v),ht (axes u),ht (axes v)]; exact Leads.pulse _ _ _ _ _
lemma peridot_rates (v : Phase (Gem G)) (i : G.ColorIndex) : cluster peridot 0 1 ![v] i= (v (0,true,i)+v (0,false,i))+(v (1,true,i)+v (1,false,i))-(v (2,true,i)+v (2,false,i))-(v (3,true,i)+v (3,false,i)) := by
  let f (v : Phase (Gem G)) := (v (0,true,i)+v (0,false,i))+(v (1,true,i)+v (1,false,i))-(v (2,true,i)+v (2,false,i))-(v (3,true,i)+v (3,false,i))
  refine Leads.buys (Leads.luster i) (q:=f) (fun u v => ?_) (fun p=> ?_) v
  · unfold f; simp [mul_sub,mul_add]; abel
  rw [show ![axes p]=axes ∘ (![p]:Fin 1 → _) by funext i; fin_cases i; rfl,line_real _ _ _ peridot_green,iteratedFDeriv_one_apply,peridot_fder]
  unfold f axes; dsimp only [Matrix.cons_val_zero]; change (((p (0,true,i)+p (0,false,i))+(p (1,true,i)+p (1,false,i))-(p (2,true,i)+p (2,false,i))-(p (3,true,i)+p (3,false,i)) : ℝ):ℂ)=_; push_cast; rfl

def fanBlade (a : PlaqAxes) (b : Fslot G) (p : Momentum) := Exterior.q p a.val.1 • axes (Lilts G (slatV b a.val.2))-Exterior.q p a.val.2 • axes (Lilts G (slatV b a.val.1))
lemma curlPulse (a : PlaqAxes) (b : Fslot G) (w : Bool) (p : Momentum) : cluster peridot 0 1 ![streamS a b p w]=fanBlade a b p := by
  ext1 i; rw [peridot_rates]
  cases w <;> simp [streamS,fanBlade,tenderOf,tenderPhi,lightFront,factor,q,axes] <;> ring
lemma first_cost_peak (v : Phase G.ColorIndex) : beat (pricePow G) 0 1 ![v]=0 := by simp [beat,enlarge,recording_apply,iteratedFDeriv_one_apply,pricePow_h.1]
lemma double_peak_cost (v w : Phase G.ColorIndex) : beat (pricePow G) 0 2 ![v,w]=dotProduct v w := by
  refine Leads.two (left_beat _) (right_beat _) (fun i u v=> ?_) (fun i u v=> ?_) (fun a b=>?_) v w
  · exact (add_dotProduct ..).trans (congrArg₂ _ rfl (smul_dotProduct ..))
  · exact (dotProduct_add ..).trans (congrArg₂ _ rfl (dotProduct_smul ..))
  rw [show ![axes a,axes b]=axes ∘ (![a,b]: Fin 2 →_) by funext i; fin_cases i <;> rfl,beat_real,pricePow_h.2]; unfold dotProduct axes; push_cast; rfl

def pencil (a : PlaqAxes) (b : Fslot G) (p : Track) := (Complex.I*(p a.val.1:ℂ)) • axes (Lilts G (slatV b a.val.2))- (Complex.I*(p a.val.2:ℂ)) • axes (Lilts G (slatV b a.val.1))
-- real ray test by limits simpler than uniform small. Later derive estimates by Ray.
lemma twin_shear {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {f : X→ℂ} (h : AnalyticAt ℝ f 0) (h0 : ∀ p:X,Tendsto (fun t : ℝ => (t:ℂ)⁻¹ * f (t • p)) cutRay (𝓝 0)) : Rays 2 f := by
  have ht (p : X) : Tendsto (fun t : ℝ => t⁻¹ • f (t • p)) cutRay (𝓝 0) := by simpa [Complex.real_smul] using h0 p
  have hv : Rays 1 f := ray_origin (fun x => ⟨0,by simpa using! ht x⟩)
  refine (rays_jet h 2).2 (fun i hi => ?_)
  interval_cases i
  · exact (rays_jet h 1).1 hv 0 (by decide)
  ext1 b; have hb := tendsto_nhds_unique (ray_limit h hv (b 0)) (show Tendsto _ cutRay (𝓝 0) from ?_)
  swap; · simpa using! ht (b 0)
  simpa [Tensor.diagonal,Tensor.coeff] using hb

lemma qPitch (a : Axis) (p : Track) : Tendsto (fun t : ℝ => (t:ℂ)⁻¹ * Exterior.q (axes (t • p)) a) cutRay (𝓝 (Complex.I*(p a:ℂ))) := by
  have ht := lift_axis_ray (roads p) (0: Fin 1) a; simp_rw [sym_one] at ht; exact ht
lemma knife_pulse (a : PlaqAxes) (b : Fslot G) (p : Track) : Tendsto (fun t : ℝ => (t:ℂ)⁻¹ • fanBlade a b (axes (t • p))) cutRay (𝓝 (pencil a b p)) := by
  unfold pencil fanBlade; simp only [smul_sub, smul_smul]
  exact ((qPitch a.val.1 p).smul_const _).sub ((qPitch a.val.2 p).smul_const _)

end curls
end YM.Stationary
end

/-!
# Leading at outgoing p, incoming k. Through field jets only where
 transported as real derivatives. `Jag` no derivative norm required here yet;
 p signs fixed by Film convention. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {G : Gauge} {P : Patch} {V : Jar G} {m : Side} {σ C : ℝ}
section arcs
-- avoid over universal Real extension of star of R matrix.
def commaQ (a : PlaqAxes) (b x y : Fslot G) (p k : Track) := dotProduct (pencil a b p) (axes (gemstone a x y)) + dotProduct (pencil a x (-(k+p))) (axes (gemstone a b y)) + dotProduct (axes (gemstone a b x)) (pencil a y k)
def corona (b x y : Fslot G) (p k : Track) := ∑ a : PlaqAxes, commaQ a b x y p k
lemma pearlRep (a : Type) [Fintype a] {v w : ℝ→ Phase a} {i j} (hv : Tendsto v cutRay (𝓝 i)) (hw : Tendsto w cutRay (𝓝 j)) : Tendsto (fun t => dotProduct (v t) (w t)) cutRay (𝓝 (dotProduct i j)) := by
  unfold dotProduct; refine tendsto_finsetSum _ fun k _ => (tendsto_pi_nhds.mp hv k).mul (tendsto_pi_nhds.mp hw k)
lemma fan_dark (a : PlaqAxes) (b : Fslot G) (p : Track) : Tendsto (fun t : ℝ => fanBlade a b (axes (t • p))) cutRay (𝓝 0) := by
  have he : Continuous (fanBlade a b) := by unfold fanBlade; refine continuous_pi fun i=> ?_; simp [q]; fun_prop
  rw [← show fanBlade a b 0=0 by simp [fanBlade,q]]; exact (he.tendsto 0).comp ((show Tendsto axes (𝓝 0) (𝓝 (0:Momentum)) by simpa using axes_maps.continuous.tendsto (0:Track)).comp (along p))
lemma stream_shrinks (a : PlaqAxes) (b : Fslot G) (w : Bool) (p : Track) : Tendsto (fun t : ℝ=> streamS a b (axes (t • p)) w) cutRay (𝓝 (streamS a b 0 w)) := (stream_diff b a w|>.continuous.tendsto 0).comp ((show Tendsto axes (𝓝 0) (𝓝 (0:Momentum)) by simpa using axes_maps.continuous.tendsto (0:Track)).comp (along p))
lemma fan_knits (a : PlaqAxes) (b c : Fslot G) (w y : Bool) (p k : Track) : Tendsto (fun t : ℝ=> cluster peridot 0 2 ![streamS a b (axes (t • p)) w,streamS a c (axes (t • k)) y]) cutRay (𝓝 (axes (gemstone a b c))) := by
  rw [← curlGem a b c w y]; refine (cluster peridot 0 2).cont.continuousAt.tendsto.comp (f:=fun t=>![streamS a b (axes (t • p)) w,streamS a c (axes (t • k)) y]) ?_
  exact tendsto_pi_nhds.mpr fun i => by fin_cases i; exacts [stream_shrinks a b w p,stream_shrinks a c y k]
lemma ternary_drops {a : Type} [Fintype a] [DecidableEq a] {f : RecordM ℂ (Fin 3) a} {X Y T : ℝ→ Phase a} {v : Phase a}
    (h : Tendsto (fun t:ℝ=> (t:ℂ)⁻¹ • X t) cutRay (𝓝 v)) (he : Tendsto Y cutRay (𝓝 0)) (ht : Tendsto T cutRay (𝓝 0)) : Tendsto (fun t:ℝ=> (t:ℂ)⁻¹ * f ![X t,Y t,T t]) cutRay (𝓝 0) := by
  let K x : Fin 3→Phase a := ![((x:ℝ):ℂ)⁻¹ • X x,Y x,T x]
  let L:=listen f
  have hb (t : ℝ) : (t:ℂ)⁻¹ * f ![X t,Y t,T t]=L (K t) := by
    change _=f (K t)
    have hy (c : ℂ) : (![c • X t,Y t,T t]:Fin 3→Phase a)= update (![X t,Y t,T t]:Fin 3→_) 0 (c • X t) := by ext1 i; fin_cases i <;> simp
    unfold K; rw [hy,f.map_update_smul,show update (![X t,Y t,T t]: Fin 3→_) 0 (X t) = ![X t,Y t,T t] by ext1 i; fin_cases i <;> simp]; rfl
  have hj : L (![v,0,0]:Fin 3→_)=0 := L.toMultilinearMap.map_coord_zero 2 (show ((![v,0,0] : Fin 3 →_) 2)=0 from rfl)
  simp_rw [hb]; rw [← hj]; refine L.cont.continuousAt.tendsto.comp (f:=K) (tendsto_pi_nhds.mpr fun i=> ?_); fin_cases i; exacts [h,he,ht]

lemma cornell_peak (b x y : Fslot G) (a : PlaqAxes) (p k : Track) : Tendsto (fun t : ℝ => (t:ℂ)⁻¹ * cornell b x y (axes (t • p)) (axes (t • k)) a) cutRay (𝓝 (commaQ a b x y p k)) := by
  let z := -(k+p)
  have he (t : ℝ) : -(axes (t • k)+axes (t • p))=axes (t • z) := by unfold z; rw [smul_neg,smul_add]; ext; simp [axes]
  let X (t : ℝ) := streamS a b (axes (t • p)) false; let Y (t : ℝ) := streamS a x (axes (t • z)) true; let T (t : ℝ) := streamS a y (axes (t • k)) true
  let M (t : ℝ) := fanBlade a b (axes (t • p)); let N (t : ℝ) := fanBlade a x (axes (t • z)); let E (t : ℝ) := fanBlade a y (axes (t • k))
  let F t u := cluster peridot 0 2 ![X (t:ℝ),u]
  let V (t : ℝ) := cluster peridot 0 2 ![Y t,T t]
  have ht q r v : beat (pricePow G ∘ peridot) 0 3 ![q,r,v]=beat (pricePow G) 0 3 ![cluster peridot 0 1 ![q],cluster peridot 0 1 ![r],cluster peridot 0 1 ![v]]+
      (dotProduct (cluster peridot 0 2 ![q,r]) (cluster peridot 0 1 ![v])+dotProduct (cluster peridot 0 1 ![r]) (cluster peridot 0 2 ![q,v]))+ dotProduct (cluster peridot 0 1 ![q]) (cluster peridot 0 2 ![r,v]) := by
    rw [upsurge _ _ peridot_green (by rw [peridot0]; exact peridot_live), peridot0, double_peak_cost, double_peak_cost, double_peak_cost, first_cost_peak, add_zero]
  have hx t : cornell b x y (axes (t • p)) (axes (t • k)) a= beat (pricePow G) 0 3 ![M t,N t,E t]+dotProduct (M t) (V t)+dotProduct (N t) (F t (T t))+dotProduct (F t (Y t)) (E t) := by
    unfold cornell; rw [he t, ht,curlPulse,curlPulse,curlPulse]; unfold M N E F X V Y T; abel
  let W (t : ℝ) := beat (pricePow G) 0 3 ![M t,N t,E t]
  simp_rw [hx,mul_add]
  have h₁ : Tendsto (fun t : ℝ => (t:ℂ)⁻¹ * W t) cutRay (𝓝 0) := ternary_drops (knife_pulse a b p) (fan_dark a x z) (fan_dark a y k)
  have h₂ := pearlRep _ (knife_pulse a b p) (fan_knits a x y true true z k)
  have h₃ := pearlRep _ (knife_pulse a x z) (fan_knits a b y false true p k)
  have h₄ := pearlRep _ (fan_knits a b x false true p z) (knife_pulse a y k)
  simp_rw [smul_dotProduct,smul_eq_mul] at h₂ h₃; simp_rw [dotProduct_smul,smul_eq_mul] at h₄
  unfold commaQ; have ht := ((h₁.add h₂).add h₃).add h₄; rw [zero_add] at ht; exact ht
lemma corona_funded (b x y : Fslot G) (p k : Track) : Tendsto (fun t : ℝ => (t:ℂ)⁻¹ * perigee b x y (axes (t • p)) (axes (t • k))) cutRay (𝓝 (corona b x y p k)) := by
  unfold corona perigee; simp_rw [mul_sum]; exact tendsto_finsetSum _ fun i _=> cornell_peak b x y i p k
end arcs
end YM.Stationary
end

/-!
# Continuum cubic in raw left components. Common Color algebra, no signed
 average on p order tests (link endpoints shift in matina). -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {G : Gauge} {P : Patch} {V : Jar G} {m : Side} {σ C : ℝ}

section gamma
lemma ad_arc (x y : G.Color) : G.ad x y= -G.ad y x := by apply G.colorMat_injective; simp [map_neg]
lemma pearl_dotted (i : G.ColorIndex) (x : G.Color) : inner ℝ (pearl i) x=x i := by
  rw [Work.F03.inner_color]; change ∑ j,(Pi.single i (1:ℝ) : Corn _) j * x j=x i; simp [Pi.single_apply,ite_mul]
lemma pearl_op (x y : G.Color) : dotProduct (axes (Lilts G x)) (axes (Lilts G y))=(inner ℝ x y:ℂ) := by
  rw [Work.F03.inner_color,Complex.ofReal_sum]; unfold dotProduct; refine sum_congr rfl fun i _ => ?_; rw [Complex.ofReal_mul]; rfl

def cosetR (i : G.ColorIndex) (x y : G.ColorIndex) := (G.ad (pearl i) (pearl y)) x
def tintX (i : G.ColorIndex) := of fun x y : G.ColorIndex => (cosetR i x y:ℂ)
lemma tintSwap (i j k : G.ColorIndex) : tintX i j k= -tintX i k j := by
  simp only [tintX,cosetR,Matrix.of_apply,← Complex.ofReal_neg]; congr 1; rw [← pearl_dotted,← pearl_dotted,real_inner_comm,Gauge.ad_skew]
lemma tintWind (i j k : G.ColorIndex) : tintX i j k=tintX j k i := by rw [tintSwap]; simp only [tintX,cosetR,Matrix.of_apply]; rw [ad_arc (pearl i)]; change -((((-(G.ad _ _)) k):ℝ):ℂ)=_; simp
-- δ with incoming dims

def deer (i j : Axis) : ℂ := if i=j then 1 else 0
def tachy (p : Track) (i : Axis) := Complex.I * (p i:ℂ)
lemma blinkV (b c : Axis) : coord b=coord c ↔ b=c := axisEquiv.injective.eq_iff
lemma marble (p : Track) (b : Axis) (x : G.ColorIndex) (a : PlaqAxes) (y : Corn G.ColorIndex) :
    dotProduct (pencil a (coord b,x) p) (axes y)=(tachy p a.val.1 * deer b a.val.2 - tachy p a.val.2 * deer b a.val.1)*(y x:ℂ) := by
  have he j : dotProduct (axes (Lilts G (slatV (coord b,x) j))) (axes y)=deer b j*(y x:ℂ) := by
    unfold deer slatV; simp only [blinkV]; by_cases h : b=j
    · subst j; simp only [↓reduceIte]; rw [← show Lilts G ((Lilts G).symm y)=y from (Lilts G).apply_symm_apply y,pearl_op,pearl_dotted]; simp
    simp [h,Ne.symm h]
  unfold pencil; rw [sub_dotProduct,smul_dotProduct,smul_dotProduct,he,he]; unfold tachy; simp only [smul_eq_mul]; ring

lemma breathOne (a : PlaqAxes) (i j : Axis) (x y : G.ColorIndex) : gemstone a (coord i,x) (coord j,y)=(if a.val=(i,j) then Lilts G (G.ad (pearl x) (pearl y)) else 0)+(if a.val=(j,i) then Lilts G (G.ad (pearl y) (pearl x)) else 0) := by
  simp only [gemstone,map_add]; refine congr_arg₂ _ ?_ ?_
  · rcases a with ⟨⟨b,c⟩,p⟩; by_cases H:b=i <;> by_cases K:c=j <;> simp [slatV,H,K,blinkV]
  rcases a with ⟨⟨b,c⟩,p⟩; by_cases H:b=j <;> by_cases K:c=i <;> simp [slatV,H,K,blinkV]

lemma cornet (i j b : Axis) (x y z : G.ColorIndex) (p : Track) : ∑ a : PlaqAxes,dotProduct (pencil a (coord b,z) p) (axes (gemstone a (coord i,x) (coord j,y)))=(tachy p i*deer b j - tachy p j*deer b i)*tintX x z y := by
  simp_rw [marble,breathOne]
  rcases lt_trichotomy i j with hi|hi|hi
  · let r : PlaqAxes:= ⟨(i,j),hi⟩; have he (a : PlaqAxes) : a.val ≠ (j,i) := fun h => let hx := a.property; by rw [h] at hx; exact hi.asymm hx
    rw [sum_eq_single r]
    · rw [if_pos rfl,if_neg (he _),add_zero]; rfl
    · intro a _ ha; rw [if_neg (fun h=> ha (Subtype.ext h)),if_neg (he _)]; simp
    simp
  · have he (a : PlaqAxes) : a.val ≠ (j,j) := fun h=> let hp := a.property; by rw [h] at hp; exact (lt_irrefl j) hp
    rw [hi]; simp [he]
  let r : PlaqAxes:=⟨(j,i),hi⟩; have he (a : PlaqAxes) : a.val ≠ (i,j) := fun h=>let ha:=a.property; by rw [h] at ha; exact hi.asymm ha
  rw [sum_eq_single r]
  · rw [if_neg (he _), if_pos rfl, zero_add, ad_arc (pearl y), map_neg,Pi.neg_apply, Complex.ofReal_neg]; change (tachy p j*_ - _)* -(tintX x z y)=_; ring
  · intro a _ ha; rw [if_neg (he _), if_neg (fun h=>ha (Subtype.ext h))]; simp
  simp
lemma deer_round (i j : Axis) : deer i j=deer j i := by simp [deer,eq_comm]
lemma coronet (i j b : Axis) (x y z : G.ColorIndex) (p k : Track) :
    corona (coord b,z) (coord i,x) (coord j,y) p k = (-(2*tachy k b+tachy p b)*deer i j + (tachy k j+ 2*tachy p j)*deer i b+(tachy k i-tachy p i)*deer j b)* tintX z x y := by
  unfold corona commaQ; rw [sum_add_distrib,sum_add_distrib]
  simp_rw [dotProduct_comm (axes _)]; rw [cornet, cornet, cornet, tintWind x z y,tintSwap z y x, deer_round b i, deer_round b j,deer_round j i]; unfold tachy; simp only [Pi.neg_apply, Pi.add_apply, Complex.ofReal_neg, Complex.ofReal_add]; ring
end gamma
end YM.Stationary
end
