import YM.MergeProof.Digits
set_option autoImplicit false
noncomputable section
namespace YM.Merge.Switch
open Function Finset Filter MeasureTheory
open scoped Topology BigOperators Classical
variable {ι:Type}

lemma Models.heading {X g:Ways ι} {f:ℝ→ℝ}{z : ℝ}(h:Models X g)(p:ι) (hp:HasDerivAt f z 0) (h0:∀ t:ℝ,X t ∅= f 0)(hx:∀ t:ℝ,X t {p}=f t) : jet X {p}=z:=by
  let F (t:ℝ):= t⁻¹*(f t-f 0)
  have ht:Tendsto F (𝓝[>] (0:ℝ)) (𝓝 z) := by simpa [F] using hp.tendsto_slope_zero.mono_left (nhdsWithin_mono _ (by simp))
  rw [h.exact]; apply tendsto_nhds_unique_of_eventuallyEq (h.converge {p}) ht
  refine approached.mono fun x hx'=> ?_; have hv: value x (g x)=X x:= h.current x ⟨hx'.1.le,hx'.2⟩
  have hz:= Switch.subtract x (g x) (Finset.mem_singleton_self p); rw [hv,hx,erase_singleton,h0] at hz -- edit
  -- use
  have he: (powerset {p}).filter (fun i=>p∈i)={{p}}:=by ext i; simp; aesop
  rw [he] at hz; simp only [sum_singleton,card_singleton,pow_one] at hz; change _=F x; unfold F; rw [hz,inv_mul_cancel_left₀ hx'.1.ne']
end YM.Merge.Switch
