import YM.Extension.UV.Station.Metric
import YM.Next.FREE_KERNELS.Differences
/-! Uniform cross-stencil prices on each fixed physical torus. Uses cover offsets as paid and old
spatial variation only along precisely those offsets; no wrap selector derivative in coupling. -/
set_option autoImplicit false
noncomputable section
open scoped Topology BigOperators Classical
namespace YM.Extension.UV.Linear
open Set Function Filter Lattice RG Laurent Bloch Metric Matrix Wilson Exterior Precision Next.Free
variable {G:Gauge} {A:Levels G} {α β : Type*} [Fintype α] [Fintype β]
local notation3 "gaugeK "=>G.slopeConstant -- remove notation unused warning
omit [Fintype α] in
def Bounded (x : α→ℝ) (c : ℝ) := ∀ i, |x i| ≤ c

def varied {S : Side} (x : Site S × α→ℝ) (d:ℝ) := ∀ i (a:α) (s:Step), |x (i+s.vec,a)-x (i,a)| ≤ d
variable {S : Side}
omit [Fintype α] in
lemma varied_wrap {x: Site S×α→ℝ} {d:ℝ} (h : varied x d) i a z : |x (i+wrap S z,a) - x (i,a)| ≤ (size z:ℝ)*d := by
  let o:=Equiv.refl Axis
  have he (w:Walk) i' (v:Cover): |x (i'+wrap S (stop v w),a)-x (i'+wrap S v,a)| ≤ (w.length:ℝ) * d := by
     induction w generalizing v with
     | nil => simp [stop]
     | cons s t ih =>
       have hp : wrap S (v+(s.vec:Cover))=wrap S v+s.vec:= by rw [map_add,wrap_vec]
       have hi := ih (v+s.vec); rw [hp, ← add_assoc] at hi
       have hx := abs_sub_le (x (i'+wrap S (stop v (s::t)),a)) (x (i'+wrap S (v+s.vec),a)) (x (i'+wrap S v,a))
       simp only [map_add,wrap_vec, ← add_assoc,List.length_cons,Nat.cast_add,Nat.cast_one] at *
       simp only [stop] at hx ⊢
       linarith only [show |x (i'+wrap S (stop (v+s.vec) t),a)-x (i'+wrap S v+s.vec,a)|≤t.length*d from by exact hi,h (i'+wrap S v) a s,hx]
  have hh := he (route (0:Cover) z o) i 0; simpa [Stationary.route_length,route_end] using hh

section rows
variable (R:Row α β) (x:Co S β→ℝ)
omit [Fintype α] in
lemma summable_entry (h:R.safe) (b:Site S) i j : Summable fun z=>R i j z*x (b+wrap S z,j):=by
   set v := ∑ i : Site S×β, |x i|
   refine Summable.of_norm_bounded ((h _ _).mul_right v) (fun z=>by rw [norm_mul,Real.norm_eq_abs (x _)]; exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f:=fun k=>|x k|) (fun k _=>abs_nonneg _) (Finset.mem_univ _)) (norm_nonneg _))

omit [Fintype α] in
lemma eval_cover (h:R.safe) (b:Site S) i : (R.acts S *ᵥ x) (b,i) = ∑ j,∑' z, R i j z * x (b+wrap S z,j):= by
   simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Row.acts, Matrix.of_apply]
   simp_rw [← tsum_mul_right]
   rw [Finset.sum_comm]
   refine Finset.sum_congr rfl fun j _=>?_;
   rw [← Summable.tsum_finsetSum (fun y _=> ?summ)]
   case summ => exact (h i j).of_norm_bounded (f:=fun z=>ite (y=b+wrap S z) (R i j z) 0) (fun z=> by split_ifs <;> [exact le_rfl; simp]) |>.mul_right _
   simp
omit [Fintype α] in
lemma apply_bound {σ C v : ℝ} (hc:0≤v) (hx:Bounded x v) (hs:0≤σ) (h:R.strip σ C): Bounded (R.acts S *ᵥ x) (Fintype.card β*v*C):= by
   have hv:=R.rights _ _ h hs
   rintro ⟨t,i⟩; rw [eval_cover R x hv t i]
   refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (g:=fun (_:β)=>C*v) (s:=Finset.univ) fun j _ => ?_).trans_eq (show (∑ j:β, C*v) = Fintype.card β*v*C by simp; ring))
   let f (z:Cover):=‖R i j z‖*v
   have hm z : ‖R i j z * x (t+wrap S z,j)‖ ≤ f z:= by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hx _) (norm_nonneg _)
   exact (norm_tsum_le_tsum_norm (summable_entry _ _ hv _ _ _ |>.norm)).trans (((Summable.tsum_le_tsum (hf:=(summable_entry _ _ hv _ _ _ |>.norm)) (hg:=(hv _ _).mul_right _) hm )).trans (by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right ((h i j).unweighted hs|>.2.2) hc))
   -- upper uses `.2.2`

omit [Fintype α] in
lemma row_varied {σ C v : ℝ} (hc:0≤v) (hx:varied x v) (hs:0≤σ) (h:R.strip σ C): varied (R.acts S *ᵥ x) (Fintype.card β*v*C):= by
   have hv:=R.rights _ _ h hs
   intro i a s
   let y(q:Co S β):=x (q.1+s.vec,q.2)-x q
   have hw := apply_bound R y hc (show Bounded y v from fun q=>hx q.1 q.2 s) hs h (i,a)
   have hy {q:Site S×α}: (R.acts S *ᵥ y) q=(R.acts S*ᵥ x) (q.1+s.vec,q.2)-(R.acts S*ᵥ x) q := by
      cases q with
      | mk q b=>
         simp_rw [eval_cover _ _ hv, ←Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun z _=>?_;
         rw [← (summable_entry _ _ hv _ _ _).tsum_sub (summable_entry _ _ hv _ _ _)]
         exact tsum_congr fun k=>by simp [y,mul_sub,add_assoc,add_comm (s.vec:Site S)]
   exact (hy (q:=(i,a))) ▸ hw
end rows

section cross
variable {f c:Side} (g : Ratio c f) (R : Cross g.count α β) (x : Co c β → ℝ) {σ C v:ℝ}
omit [Fintype α] in
lemma cross_bound (hv:0≤v)(hx:Bounded x v) (hs:0≤σ) (h:R.strip σ C) : Bounded (installed g R *ᵥ x) (Fintype.card β*v*C) := fun i=> by change |(R.acts c *ᵥ x) ((splitCo g α) i)| ≤ _; exact apply_bound R x hv hx hs h (splitCo g _ i)

omit [Fintype α] in
lemma cancel_entry (hv:0≤v) (hx:varied x v) (hs:0<σ) (h:R.strip σ C) (hz:∀ a : β, installed g R *ᵥ (fun q=> if q.2=a then (1:ℝ) else 0) = 0) :
    Bounded (installed g R *ᵥ x) (Fintype.card β*(1/σ)*v*C):= by
   have hr:=R.rights _ _ h hs.le
   have hp := eval_cover R x hr
   intro i
   obtain ⟨r,a,hi⟩:= (show ∃ r a, splitCo g α i=(r,a) from by exact ⟨(splitCo g α i).1,(splitCo g α i).2,rfl⟩)
   have hz (b:β) : ∑' z,R a b z=0:= by
     let y : Site c × β→ℝ:= fun k=>if k.2=b then 1 else 0
     have h₀ := eval_cover R y hr r a
     have hx : (R.acts c*ᵥ y) (r,a)=0:= hi ▸ congr_fun (hz b) i
     simp only [hx,y,mul_ite,mul_one,mul_zero] at h₀; have he j : (∑' z, ite (j=b) (R a j z) 0)=(if j=b then ∑' z,R a j z else 0):= by split_ifs with h <;> simp [h]
     simpa only [he,Finset.sum_ite_eq',Finset.mem_univ,if_true] using h₀.symm
   suffices |(R.acts c*ᵥ x) (splitCo g _ i)| ≤ _ from this
   rw [hi,hp]; refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (g:=fun _=> C*(1/σ)*v) (s:=Finset.univ) fun b _=>?_).trans_eq (show (∑ b:β,C*(1/σ)*v) = Fintype.card β*(1/σ)*v*C by simp; ring))
   let y : Co c β→ℝ := fun q=>x q-x (r,b)
   have heq : (∑' z,R a b z*x (r+wrap c z,b))=∑' z,R a b z*y (r+wrap c z,b):= by
       have he:= (summable_entry R y hr r a b).tsum_add ((hr a b).of_norm.mul_right (x (r,b)))
       convert he using 1; · refine tsum_congr fun i=>?_; unfold y; ring
       rw [tsum_mul_right,hz,zero_mul,add_zero]
   have hn z : ‖R a b z * y (r+wrap c z,b)‖ ≤ (v/σ)*(Real.exp (σ*size z)*‖R a b z‖) := by
       have hh:= varied_wrap hx r b z
       have he: (size z:ℝ)*v ≤ Real.exp (σ*size z)*(v/σ):=
          calc _ ≤ (Real.exp (σ*size z)/σ)*v := mul_le_mul_of_nonneg_right ((le_div_iff₀ hs).mpr ((by linarith : (size z:ℝ)*σ ≤ σ*size z+1).trans (Real.add_one_le_exp _))) hv
               _ = _ := by ring
       rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hh.trans he) (norm_nonneg _) |>.trans_eq (by ring)
   have hsum:=h a b|>.2.1
   rw [heq]; exact (norm_tsum_le_tsum_norm ((hsum.mul_left _).of_nonneg_of_le (fun _=>norm_nonneg _) hn)).trans (Summable.tsum_le_tsum (hf:=(summable_entry R y hr r a b|>.norm)) (hg:=hsum.mul_left _) hn|>.trans (by rw [tsum_mul_left]; exact (mul_le_mul_of_nonneg_left (h a b|>.2.2) (div_nonneg hv hs.le)).trans_eq (by ring)))
end cross
end YM.Extension.UV.Linear
