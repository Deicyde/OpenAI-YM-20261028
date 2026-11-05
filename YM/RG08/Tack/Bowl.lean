import YM.RG08.Tack.Loops
/-! # Exact quadratic receipt (physical normalized color and 2!). -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Tack
open Filter Lattice RG Wilson Forms Pert.Bulk Isles Camera Carrel Glyph Room Exterior Function
open Stationary Bloch Laurent Precision Line Finset Bid Work.F03 Matrix
open AnalyticNext.QuarticMatch.Radius Articles Model
open scoped BigOperators Classical ContDiff Topology Matrix Matrix.Norms.Frobenius NNReal InnerProductSpace

variable {G:Gauge}{c f:Side}{S:StepData c f}{P:Patch}{K:KernelChoices}
attribute [local instance] Gauge.frobInner

def missing (S:StepData c f)(e:Edge (Site c))(w:Cellar (Epic S.patch G c)):G.Color:= (high S w) (e.1,coord e.2)-WithLp.toLp 2 (fun j=> (probe S *ᵥ parts G 1 (low S w) j) (e.1,coord e.2))
def diff (S:StepData c f)(t:S.Choices)(e:Edge (Site c))(w:Cellar (Epic S.patch G c)):=represent (high S w) e*(S.prediction (represent (low S w)) t e)⁻¹
lemma missing_add (S:StepData c f)(u v:Cellar (Epic S.patch G c)) (e:Edge (Site c)):missing S e (u+v)=missing S e u+missing S e v:=by unfold missing; rw [map_add,map_add,Pi.add_apply];simp_rw [parts_add, mulVec_add];have he {x y:G.ColorIndex→ℝ}:WithLp.toLp 2 (x+y)=WithLp.toLp 2 x+WithLp.toLp 2 y:=rfl;change _-WithLp.toLp 2 ( (fun _x:G.ColorIndex=>(_ :ℝ)) + (fun _x:G.ColorIndex=>(_ :ℝ)))=_;rw [he];abel
lemma birth (h:S.patch.Branches S.kernel G)(t:S.Choices)(e:Edge (Site c)) :diff (G:=G) S t e 0=1:=by simp [diff,link_one,Push.settled S h]
lemma touch (h:S.patch.Branches S.kernel G)(t:S.Choices)(e:Edge (Site c))(w:Cellar (Epic S.patch G c)): HasDerivAt (fun x:ℝ=>G.mat (diff S t e (x • w))) (G.colorMat (missing S e w)) 0:=by
 have ht:=Push.prices S h e t (low S w)
 have hh:=Work.F03.represent_rate (high S w) e
 unfold diff; simp only [G.mat_mul,G.mat_inv,map_smul]
 convert! (hh.mul ht.star) using 1
 simp [zero_smul,link_one,Push.settled S h,G.mat_one,missing,G.colorMat_skew,sub_eq_add_neg]

lemma gulp (h:S.patch.Branches S.kernel G)(t:S.Choices)(e:Edge (Site c))(w:Cellar (Epic S.patch G c)) : Tendsto (fun x:ℝ=>ask S t e.2 e.1 (x • w)/ x^2) (𝓝[≠] 0) (𝓝 (S.kernel.penalty * inner ℝ (missing S e w) (missing S e w) /2)):=by
 rw [real_inner_self_eq_norm_sq,mul_div_assoc]
 simp_rw [ask,mul_div_assoc]; exact (price_limit (V:=fun x=>diff S t e (x • w)) (by rw [zero_smul,birth h]) (touch h t e w)).const_mul _

lemma bowls (h:S.patch.Branches S.kernel G)(t:S.Choices)(e:Edge (Site c)):
  ask (G:=G) S t e.2 e.1 0=0 ∧ fderiv ℝ (ask (G:=G) S t e.2 e.1) 0=0 ∧ ∀ u v:Cellar (Epic S.patch G c), iteratedFDeriv ℝ 2 (ask S t e.2 e.1) 0 ![u,v]= S.kernel.penalty* inner ℝ (missing S e u) (missing S e v):=by
 apply hessian_of_limit ((ask_pace h t e.2 e.1).of_le le_top) (gulp h t e)
 · intro x y z; rw [missing_add,inner_add_left,mul_add]
 intro x y;rw [real_inner_comm (missing S e x)]
lemma bowl_low (h:S.patch.Branches S.kernel G)(t:S.Choices)(e:Edge (Site c)):Low 2 (flask (ask (G:=G) S t e.2 e.1)):=by
 intro i hi
 obtain ⟨ht,hP,_⟩:=bowls h t e
 rcases show i=0∨i=1 by omega with rfl|rfl
 · simp [tap,flask,Camera.print,ht]
 rw [flute, Camera.print];unfold Camera.wedge
 -- wedge at 0
 simp [Camera.print,hP]

lemma bowl_eval (h:S.patch.Branches S.kernel G)(t:S.Choices)(e:Edge (Site c))(w:Cellar (Epic S.patch G c)):
 MvPolynomial.eval w (tap 2 (flask (ask S t e.2 e.1)))= S.kernel.penalty * inner ℝ (missing S e w) (missing S e w)/2:=by
 rw [glimpses (ask_pace h _ _ _),show (fun _:Fin 2=>w)=![w,w] from funext (fun i=>by fin_cases i <;> rfl), (bowls h t e).2.2 w w];norm_num;ring
lemma fare_low (h:S.patch.Branches S.kernel G)(t:S.Choices):Low 2 (flask (fair (G:=G) S t)):=by
 intro i hi; unfold fair
 have hh(y:Axis):Pace (∑ x:Site c,ask (S) t y x (G:=G)):=Pace.metal _ _ fun _ _=>ask_pace h t _ _
 rw [slurry _ _ (fun i _=>hh i),tap,map_sum]; apply sum_eq_zero; intro a _;rw [slurry _ _ (fun j _=>ask_pace h t ..),map_sum];apply sum_eq_zero;intro b _;exact bowl_low h t (b,a) i hi
lemma taxed (h:S.patch.Branches S.kernel G)(t:S.Choices)(w:Cellar (Epic S.patch G c)):
 MvPolynomial.eval w (tap 0 (tax 2 (flask (fair S t))))= S.kernel.penalty/2 * ∑ e:Edge (Site c),inner ℝ (missing S e w) (missing S e w):=by
 rw [audited];simp only [fair,Nat.zero_add];have hh(y:Axis):Pace (∑ x:Site c,ask (S) t y x (G:=G)):=Pace.metal _ _ fun _ _=>ask_pace h t _ _
 rw [slurry _ _ (fun i _=>hh i),tap,map_sum,map_sum];simp_rw [slurry _ _ (fun (b:Site c) _=>ask_pace h t _ _),map_sum]; rw [Finset.sum_comm,Fintype.sum_prod_type, Finset.mul_sum];apply Finset.sum_congr rfl;intro v _;rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro i _
 change MvPolynomial.eval w (tap _ _)=_;rw [show MvPolynomial.eval w (tap 2 (flask (ask S t i v)))=_ from bowl_eval h t (v,i) w];ring
end YM.RG08.Tack
