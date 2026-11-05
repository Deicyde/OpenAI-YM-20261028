import YM.FullVolume.Ray.Burst
import YM.FullVolume.Ray.Anchor
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hem
import YM.Planned.ATOM_REGULAR_ESTIMATE.CrossEffect
import YM.Next.FOUNDATIONS.LinkBounds
/-! Mixed real probes, Scout in poly-radius g, pointed Shape on real V. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Ray
open Filter Function Set RG ConnectedActivityE6.Blaze Planned.AtomRegular Next.Foundations
open scoped Topology BigOperators NNReal ContDiff
variable {a b p c d v:ℝ} {E F: Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {g : ℝ→E→F} {x : E} {k i n:ℕ}
abbrev tintM (x u:E) (t:ℝ):=x+t•u
lemma sheen {f:E→F} (h:ContDiffAt ℝ k f x) (v:E) : ContDiffAt ℝ k (f ∘ tintM x v) 0:= (show ContDiffAt ℝ k f (tintM x v 0) from by unfold tintM; simpa).comp _ (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
def marked (n:ℕ) (f:E→F) (x u:E):= iteratedDeriv n (f ∘ tintM x u) 0
lemma compass {f:E→F} (p:ContDiffAt ℝ k f x) (v:E) : marked k f x v= YM.Tensor.diagonal (iteratedFDeriv ℝ k f x) v:= by
  let g i:= f (x+i)
  have h: ContDiffAt ℝ k g 0:=(show ContDiffAt ℝ k f (x+0) from by simpa).comp (0:E) (show ContDiffAt ℝ k (fun i:E=>x+i) 0 from (by fun_prop))
  have ht:= iteratedDeriv_on_line h v; unfold g at *; rw [iteratedFDeriv_comp_add_left,add_zero] at ht; exact ht
lemma point_norm {f:E→F} (p:Brush k a b f x) (h:i≤k) {v:E} (ht:‖v‖≤1): ‖marked i f x v‖ ≤ a*b^i:=by
  rw [compass (p.smaller h).smooth v]
  apply (ContinuousMultilinearMap.le_opNorm ..).trans
  apply (mul_le_of_le_one_right (norm_nonneg _) ?_).trans (p.order i h); exact Finset.prod_le_one (fun _ _=>norm_nonneg _) (fun _ _=>ht)
structure Weigh (k : ℕ) (x : E) (p a b:ℝ) (f:ℝ→E→F) :Prop where
  slope : 0≤b
  smooth : ∀ i∈sun, ContDiffAt ℝ k (f i) x
  probes (u:E): ‖u‖≤1 → ∀ i:ℕ, i≤k → Scout p (fun t=> marked i (f t) x u) (a*b^i)
namespace Weigh
lemma ray (h:Weigh k x p a b g): 1 ≤ p:= (h.probes 0 (by simp) _ (Nat.zero_le k)).ray
lemma nonneg (h:Weigh k x p a b g): 0≤a:= by simpa using (h.probes 0 (by simp) _ (Nat.zero_le k)).nonneg
lemma loses (h:Weigh k x p a b g) (ht:a≤c) (hp:b≤d):Weigh k x p c d g:=
  ⟨h.slope.trans hp,h.smooth,fun x hx i hi=> (h.probes x hx i hi).enlarged (mul_le_mul ht (pow_le_pow_left₀ h.slope hp i) (pow_nonneg h.slope _) (h.nonneg.trans ht))⟩
lemma cong {f:ℝ→E→F} (h:Weigh k x p a b g) (he:∀ i∈sun,f i=ᶠ[𝓝 x] g i):Weigh k x p a b f:=by
  refine ⟨h.slope, fun i hi=> (h.smooth i hi).congr_of_eventuallyEq (he _ hi),fun y hy j hj=> (h.probes y hy j hj).replace fun i hi=> ?_⟩
  dsimp only
  have ht := (h.smooth i hi).of_le (show (j:WithTop ℕ∞) ≤ (k:WithTop ℕ∞) from (by exact_mod_cast hj))
  rw [compass ht,compass (ht.congr_of_eventuallyEq (he _ hi)), ((he _ hi).iteratedFDeriv ℝ j).eq_of_nhds]
lemma still {f:E→F} (h:Brush k a b f x) (hp:1≤p): Weigh k x p a b (fun _=>f) := ⟨h.pos,fun _ _=>h.smooth,fun u hu i hi=> (Scout.still hp _).enlarged (point_norm h hi hu)⟩
lemma zero (hp:1≤p)(hb:0≤b): Weigh k x p 0 b (fun _ _=> (0:F)):= still (by simpa using Brush.certified (k:=k) hb (0:F)) hp
section scalar
variable {f g : ℝ → E→ℝ}
lemma dual (h:Weigh k x p a b f) (hv:Weigh k x p c d g) : Weigh k x p (a*c) (b+d) (fun i y=>f i y*g i y):=by
  refine ⟨add_nonneg h.slope hv.slope,fun i hi=> (h.smooth i hi).mul (hv.smooth i hi),?_⟩
  intro u hu j hj
  let s:=Finset.range (j+1); let R i n:=(j.choose i:ℝ)*marked i (f n) x u*marked (j-i) (g n) x u; let P i:=(j.choose i:ℝ)*(a*b^i)*(c*d^(j-i))
  have ht (i) (hi:i∈s): Scout p (R i) (P i):=by
    have hh:i≤j:=by have h:= Finset.mem_range.mp hi; omega
    have he:= ((h.probes u hu i (hh.trans hj)).scale (j.choose i : ℝ)).multiplies (hv.probes u hu (j-i) (by omega))
    rw [Real.norm_natCast] at he; exact he
  refine ((Scout.pieces s R P h.ray ht).enlarged ?_).replace ?_
  · unfold P s; rw [add_pow,Finset.mul_sum]; apply Finset.sum_le_sum; intro i _; apply le_of_eq; ring
  intro t hm; dsimp only [marked,R]; symm
  exact iteratedDeriv_fun_mul (sheen ((h.smooth t hm).of_le (Nat.cast_le.mpr hj)) u) (sheen ((hv.smooth t hm).of_le (Nat.cast_le.mpr hj)) u)
lemma prod {ι:Type*} [DecidableEq ι] (s:Finset ι) (f:ι→ℝ→E→ℝ) (a b:ι→ℝ) (hp:1≤p) (h:∀ i∈s, Weigh k x p (a i) (b i) (f i)): Weigh k x p (∏ i∈s,a i) (∑ i∈s,b i) (fun t y=>∏ i∈s,f i t y):=by
  induction s using Finset.induction_on with
  | empty=> simpa using still (Brush.certified (x:=x) (k:=k) (le_refl 0) (1:ℝ)) hp
  | insert z s hz ih => simp_rw [Finset.prod_insert hz, Finset.sum_insert hz]; exact (h _ (Finset.mem_insert_self ..)).dual (ih fun i hi=> h i (Finset.mem_insert_of_mem hi))
end scalar

def pattern (k : ℕ) : ℝ:= ∑ i∈Finset.range (k+1), polarCost i
variable [CompleteSpace F]
lemma timber (h:Weigh k x p a b g) (w:Rung) (v:ℝ) (hv:∀ i:ℕ, ‖trace w (fun x=>(x/p)^i)‖ ≤ v): Brush k (pattern k*(v*a)) b (fun y=>trace w (fun t=>g t y)) x:=by
  let f y:= trace w (fun t=> g t y); have hv':0≤v:= (norm_nonneg _).trans (hv 0)
  have hf : ContDiffAt ℝ k f x:= ContDiffAt.sum (fun i (_:i∈w.support)=> (h.smooth i i.2).const_smul _)
  refine ⟨hf,h.slope,fun i hi=> ?_⟩
  have hP := hf.of_le (Nat.cast_le (α:=WithTop ℕ∞)|>.mpr hi)
  have hn:0≤ v*(a*b^i):= mul_nonneg hv' (mul_nonneg h.nonneg (pow_nonneg h.slope _))
  have hz := op_polar (k:=i) (YM.Analysis.sym_Jet hP) hn
  apply (hz ?_).trans
  · rw [mul_assoc, mul_assoc v a]; refine mul_le_mul_of_nonneg_right ?_ hn; unfold pattern; exact Finset.single_le_sum (a:=i) (s:=Finset.range (k+1)) (fun j _=>zero_le_one.trans (polar_one j)) (Finset.mem_range.mpr (by omega))
  intro y hy; rw [← compass hP,show marked i f x y=trace w (fun t=> marked i (g t) x y) from ?_]
  · exact (h.probes y hy i hi).beam w v hv
  let V j:= g j ∘ tintM x y
  have hV (j:sun): ContDiffAt ℝ i (V j) 0:= sheen ((h.smooth j j.2).of_le (Nat.cast_le.mpr hi)) y
  unfold trace marked f; rw [show ((fun z=> trace w (fun t=>g t z))∘tintM x y) = (fun j=>∑ i∈w.support,w i • V i j) from rfl,
    iteratedDeriv_fun_sum (fun i (_:i∈w.support)=> (hV i).const_smul _)]
  simp_rw [iteratedDeriv_fun_const_smul (hV _)]; rfl
end Weigh
end YM.FullVolume.Ray
