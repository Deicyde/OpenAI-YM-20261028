import YM.UVExtension.Lamppost.Spice
import Mathlib.Analysis.Complex.TaylorSeries

/-! Propagation of linear properties (identities and measurability in the original
    REAL integration variables) from holomorphy in the parameters. No uniform budgets needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lamppost
open Complex Filter Metric Function Topology MeasureTheory Set
open scoped BigOperators ContDiff Classical NNReal ENNReal
variable {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

structure Husk (P : (A→E) → Prop) : Prop where
  zero : P 0
  plus : ∀ f g, P f → P g → P (f+g)
  scale : ∀ t:ℂ, ∀ f, P f → P (t • f)
  union : ∀ {F:ℕ → A → E} {f}, (∀ᶠ i:ℕ in atTop,P (F i)) → (∀ a, Tendsto (fun i=> F i a) atTop (𝓝 (f a))) → P f

namespace Husk
variable {F : ℂ→ A→ E} {P : (A→E) → Prop}
omit [CompleteSpace E] in
lemma adds {K:Type*} (h:Husk P) (f:K→A→E) (k:Finset K) (hp:∀ i∈k,P (f i)) : P (fun i=> ∑ j∈k,f j i) := by
  induction k using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using! h.zero
  | insert a k ha hh => simp_rw [Finset.sum_insert ha]; exact h.plus _ _ (hp a (Finset.mem_insert_self ..)) (hh fun i hi=> hp i (Finset.mem_insert_of_mem hi))

variable {s u : Set ℂ} {c : ℂ} {r : ℝ}
lemma poppet (hp : Husk P) (hr : 0<r) (h : ∀ a, DifferentiableOn ℂ (fun z=>F z a) (ball c r))
    (hh : ∃ b:ℂ,b≠0 ∧ ∀ᶠ t:ℝ in 𝓝 0,P (F (c+t*b))) {z} (hz:z ∈ ball c r) : P (F z) := by
  obtain ⟨v,hv,hs⟩:= hh; let f a z:= F z a
  let g(t:ℝ):= c+t*v
  obtain ⟨w,hw,hW,hZ⟩:= _root_.mem_nhds_iff.mp (hs.and (show ∀ᶠ t:ℝ in 𝓝 0,g t∈ball c r from (by
    have he:= (show Continuous g from continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).tendsto 0; rw [show g 0=c by simp [g]] at he
    exact he.eventually (ball_mem_nhds c hr))))
  have he (i:ℕ) : ∀ t∈w,P (fun a => iteratedDeriv i (f a) (g t)) := by
    induction i with
    | zero => intro t ht; simp only [iteratedDeriv_zero]; exact (hw ht).1
    | succ i ih =>
      intro t ht
      obtain ⟨r,R,hq,Q⟩ := exists_seq_strictAnti_tendsto t
      have hC:g.Injective:= fun x y h=> Complex.ofReal_injective (mul_right_cancel₀ hv (add_left_cancel h))
      have ht' := ((show Continuous g by unfold g; fun_prop).tendsto t).comp Q
      let d (x:ℂ) a:= iteratedDeriv i (f a) x
      apply hp.union (F:=fun n:ℕ=> (g (r n)-g t)⁻¹ • (d (g (r n)) -d (g t)))
      · filter_upwards [Q.eventually (hW.mem_nhds ht)] with n hn
        apply hp.scale; rw [sub_eq_add_neg (d _) (d _),← neg_one_smul ℂ (d (g t))]; exact hp.plus _ _ (ih _ hn) (hp.scale _ _ (ih _ ht))
      intro a; simp only [iteratedDeriv_succ]
      have hA : AnalyticAt ℂ (iteratedDeriv i (f a)) (g t):= by rw [iteratedDeriv_eq_iterate]; exact ((h a).analyticAt (isOpen_ball.mem_nhds (hw ht).2)).iterated_deriv i
      refine (hasDerivAt_iff_tendsto_slope.mp hA.differentiableAt.hasDerivAt).comp (tendsto_nhdsWithin_iff.mpr ⟨ht',?_⟩)
      filter_upwards with n; exact hC.ne (hq n|>.ne')
  have hh n : P (fun a=> iteratedDeriv n (f a) c) := by
    simpa only [g, ofReal_zero,zero_mul,add_zero] using he n 0 ‹_›
  let c' n a:=(n.factorial:ℂ)⁻¹ • (z-c)^n • iteratedDeriv n (f a) c
  apply hp.union (F:=fun n a=> ∑ i∈Finset.range n,c' i a) (Eventually.of_forall fun n=> hp.adds c' _ (fun i _=> hp.scale _ _ (hp.scale _ _ (hh i))))
  exact fun a=> (hasSum_taylorSeries_on_ball (h a) hz).tendsto_sum_nat

lemma invades (hp:Husk P) (h : IsOpen s) (he:IsPreconnected s) (hf : ∀ i, DifferentiableOn ℂ (fun z=> F z i) s)
    (hz : c∈s) (hu: ∀ᶠ t:ℝ in 𝓝 0,P (F (c+t))) {z} (hx:z∈s) : P (F z) := by
  let v:= interior {w | P (F w)}
  have hV : c∈v:= mem_interior_iff_mem_nhds.mpr (by
    obtain ⟨r,hr,hR⟩:=nhds_basis_ball.mem_iff.mp (h.mem_nhds hz); filter_upwards [ball_mem_nhds c hr] with y hy
    exact poppet hp hr (fun i=> (hf i).mono hR) ⟨1,one_ne_zero,by simpa using hu⟩ hy)
  have hZ {t} (ht:t∈s) (hg:t∈closure v): t∈v:= mem_interior_iff_mem_nhds.mpr (by
    obtain ⟨r,hr,hR⟩:= nhds_basis_ball.mem_iff.mp (h.mem_nhds ht)
    let d:=r/4; have hd:0<d:=by unfold d; positivity
    obtain ⟨w,hw,hW⟩:= mem_closure_iff_nhds.mp hg _ (ball_mem_nhds t hd)
    have hh : ball w (2*d) ⊆ s:= by
      intro y hy; apply hR; rw [mem_ball]; have hv:= dist_triangle y w t; rw [mem_ball] at hw hy; unfold d at *; linarith
    have he : ∀ᶠ e:ℝ in 𝓝 0,P (F (w+e)):= by
      let g (t:ℝ):=w+t; have hx:Continuous g:= continuous_const.add Complex.continuous_ofReal; have ht:= hx.tendsto 0
      rw [show g 0=w by simp [g]] at ht; exact ht.eventually (mem_interior_iff_mem_nhds.mp hW)
    filter_upwards [ball_mem_nhds t hd] with y hy; refine poppet hp (mul_pos (by norm_num) hd) (fun i=> (hf i).mono hh) ⟨1,one_ne_zero,by simpa⟩ ?_
    rw [mem_ball]; change y∈ball t d at hy; rw [mem_ball,dist_comm] at hw; rw [mem_ball] at hy; linarith [dist_triangle y t w])
  apply interior_subset (s:={w | P (F w)})
  by_contra ha
  have hh:= he v (closure v)ᶜ isOpen_interior (isClosed_closure.isOpen_compl)
    (fun t ht=> by by_cases hv:t∈closure v; exact Or.inl (hZ ht hv); exact Or.inr hv)
    ⟨c,hz,hV⟩ ⟨z,hx,fun hv=>ha (hZ hx hv)⟩
  obtain ⟨i,_,hK⟩:= hh; exact hK.2 (subset_closure hK.1)
end Husk
end YM.UVExtension.Lamppost
