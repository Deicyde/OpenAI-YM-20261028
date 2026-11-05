import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Tablet
import YM.Further.DENSE_MIXED_KERNELS.Hall
import YM.Further.DENSE_MIXED_KERNELS.Stroke
import YM.Push.ABSOLUTE_SUMS.Copies
import YM.Push.ABSOLUTE_SUMS.FiniteLog

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented  Sector Footprint Packets SliceRows Control Window Pulse
open Coat  ProbabilityTheory Poll  Mixed Census Blaze     Corona Brush   Tablet        Poll  
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
namespace Charity
open Gas Multiple Ursell Trees  
-- Permit simultaneous budgets in PG Tide.Param.T workspace not spent separately for each point. Stamp sold all neighborhoods.
structure Est (w ζ x : ℝ)(f:ℝ→ℝ): Prop where
  alive : HasDerivAt f (deriv f x) x
  credit : 0 ≤ ζ
  bill : ∃ a b : ℝ,0≤a ∧ 0≤b ∧ a+b≤w ∧ |f x|≤a ∧ |deriv f x| ≤ ζ*b
namespace Est
variable {a b z x D u w : ℝ}{f g :ℝ→ℝ}
lemma nil (a u v x : ℝ)(ha:0≤u)(he:|a| ≤ v):Est v u x fun _=>a:= ⟨(by simp only [deriv_const']; exact hasDerivAt_const x a),ha,⟨v,0,(abs_nonneg _).trans he,le_rfl,by simp,he,by simp⟩⟩
lemma upto (h:Est a u x f)(hc:a≤w):Est w u x f:=by obtain ⟨q,V,h₁,h₂,h₃,h₄⟩:=h.bill; exact ⟨h.alive,h.credit,q,V,h₁,h₂,h₃.trans hc,h₄⟩
lemma value (h:Est a u x f) : ‖f x‖ ≤ a:=by obtain ⟨q,V,h₁,h₂,h₃,h₄⟩:=h.bill; exact h₄.1.trans ((le_add_of_nonneg_right h₂).trans h₃)
lemma high (h:Est a u x f): ‖deriv f x‖ ≤ u*a:= by obtain ⟨q,V,h₁,h₂,h₃,h₄⟩:=h.bill; exact h₄.2.trans (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left h₁).trans h₃) h.credit)
lemma good (h : Est a u x f):0≤a:= (norm_nonneg _).trans h.value
lemma mold (h : Est a u x f)(H:Est b u x g):Est (a*b) u x (fun t=> f t*g t):=by
  obtain ⟨q₁,q₂,h₁,h₂,hq,hf,hG⟩:=h.bill; obtain ⟨b₁,b₂,hB,hB',hb,hV,hU⟩:= H.bill
  let w:= q₁*b₂+q₂*b₁; have hh : 0≤w:=add_nonneg (mul_nonneg h₁ hB') (mul_nonneg h₂ hB)
  let F:=deriv (fun t=> f t*g t) x; have he : F = deriv f x*g x+f x* deriv g x := (h.alive.mul H.alive).deriv
  refine ⟨(h.alive.mul H.alive).differentiableAt.hasDerivAt,h.credit, q₁*b₁,w,mul_nonneg h₁ hB,hh,?_ ,?_,?_⟩
  · refine le_trans ?_ (mul_le_mul hq hb (add_nonneg hB hB') h.good); unfold w; nlinarith
  · rw [abs_mul]; exact mul_le_mul hf hV (abs_nonneg _) h₁
  change |F| ≤ _; rw [he];
  calc
    |deriv f x*g x+f x*deriv g x| ≤ |deriv f x*g x|+|f x*deriv g x| := abs_add_le ..
    _ = |deriv f x| * |g x|+|f x| * |deriv g x|:= by simp only [abs_mul]
    _ ≤ u*q₂*b₁+q₁*(u*b₂):= by gcongr; exact mul_nonneg h.credit h₂
    _ = u*w:=by unfold w; ring
lemma rescale (h:Est a u x f) (v : ℝ) : Est (|v| * a) u x (fun t=>v*f t):= mold (nil _ _ _ _ h.credit le_rfl) h
lemma perennial (h:Est a u x f) (i:ℕ) : Est (a^i) u x (fun t=> (f t)^i):=by
  induction i with
  | zero => simp only [pow_zero]; exact nil _ _ _ _ h.credit (by norm_num)
  | succ i ih=>simp_rw [pow_succ]; exact ih.mold h
lemma summit {i:Type*} (X : Finset i) (f:i→ℝ→ℝ)(a:i→ℝ)(hu:0≤u)(H:∀ i∈X,Est (a i) u x (f i)): Est (∏ i∈X,a i) u x (fun v=>∏ i∈X, f i v):=by
    induction X using Finset.induction_on with
    | empty=>simpa using nil 1 u 1 x hu (by norm_num)
    | @insert i s hs h=> simp_rw [prod_insert hs]; exact (H i (mem_insert_self ..)).mold (h (fun i hi=> H _ (mem_insert_of_mem hi)))
lemma tilted (x f g a b d : ℝ) (h: |f|≤a) (hv: |g|≤d*b) (ht: |x| * d≤1)(he:0≤b)(hd:0≤d) : Est (a+2*b) d x (fun i=> f+i*g) :=by
  have hG : HasDerivAt (fun i:ℝ=> f+i*g) g x:=by simpa using ((hasDerivAt_id' x).mul_const g).const_add f
  refine ⟨?_ ,hd,a+b,b,add_nonneg ((abs_nonneg _).trans h) he,he,by linarith,?_ ,?_⟩
  · rw [hG.deriv]; exact hG
  · apply (abs_add_le ..).trans (add_le_add h _); rw [abs_mul]; exact (mul_le_mul_of_nonneg_left hv (abs_nonneg _)).trans (by rw [←mul_assoc]; exact mul_le_of_le_one_left he ht)
  rw [hG.deriv]; exact hv
variable {ι κ : Type*}
lemma logCharge (R : ι→ι→Prop) (u:ι→ℝ)(F: ℝ→ι→ℝ)(hq:0≤D)(h:∀i,Est (u i) D x (fun t=>F t i))(r:Clusters ι):Est (clusters R u r.2) D x (fun i=>Gas.term R (F i) r):=by
  have hv:= Est.summit univ (fun i t=> F t (r.2 i)) (fun i=> u (r.2 i)) hq (fun i _=> h (r.2 i))
  let c:ℝ:=coefficient R r.2; let t:ℝ:=↑(r.1+1).factorial
  have hZ : clusters R u r.2= (|c/t| * (∏ i,u (r.2 i))) :=by rw [abs_div, abs_of_nonneg (by unfold t; positivity : 0≤ t)]; change ((|c| * _)/t:_)= _; ring
  rw [hZ,show (fun i=> Gas.term R (F i) r)= (fun i=>c/t* ∏ j,F i (r.2 j)) from funext fun _=>by unfold Gas.term c t; ring]
  exact hv.rescale _
lemma copies (F:ℝ→ι→ℝ)(u:ι→ℝ)(hz:0≤D)(he:∀ i, Est (u i) D x (fun s=>F s i))(r : Reps ι): Est (manyW u r) D x (fun i=> manyW (F i) r):=by
  unfold manyW; refine Est.summit univ _ _ hz fun i _=> ?_; let n:=r.2 i+1
  simp_rw [div_eq_mul_inv,mul_comm _ _⁻¹]; simpa only [abs_inv, abs_of_pos (by positivity : 0<((n.factorial:ℕ):ℝ))] using! (((he i.val).perennial n).rescale (n.factorial:ℝ)⁻¹)
lemma seqOwnUp (p : Set ℝ) (hp:IsOpen p)(hx:x∈p)(hk:IsPreconnected p) (f:ι→ℝ→ℝ)(c:ι→ℝ)(h:Summable c)
    (he:∀ i,∀ s∈p, Est (c i) D s (f i)) : HasDerivAt (fun s=> ∑' i,f i s) (∑' i, deriv (f i) x) x:=by
  exact hasDerivAt_tsum_of_isPreconnected (t:=p) (g:=f) (g':=fun i=> deriv (f i)) (y₀:=x) (h.mul_left D) hp hk (fun i s hs=> (he i s hs).alive) (fun i s hs => (he i s hs).high) hx (Summable.of_norm_bounded h (fun i=> (he i x hx).value)) hx
end Est
end Charity
end YM.PhysicalNext.Repeat.Daisy
