import YM.Contacts.Normal.Fans
/-!
# Shell partition and accounting
Use on all cutoff or small-shell-supported tests. Absolute dyadic decomposition together with
angular fans here. Coordinates as above; no dyadic partitions appear in the definition.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Contacts.Normal
open Function Filter Set Metric MeasureTheory Submodule MultipleContact
open scoped Topology ContDiff Classical BigOperators InnerProductSpace
variable {E F Z : Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
section common
variable (K : Submodule ℝ E)
def eclipse (r : ℝ) := window K r-window K (r/2)
omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
lemma support_comp [TopologicalSpace F] [Zero Z] (u : E→F)(hu : Continuous u)(f:F→Z) : tsupport (f ∘ u) ⊆ u ⁻¹' tsupport f:= closure_minimal (fun x h=>subset_closure (show u x ∈ Function.support f from h)) ((isClosed_tsupport _).preimage hu)
omit [FiniteDimensional ℝ E] in
lemma support_mask (f v : SmoothTests E) : tsupport (mask f v).val ⊆ tsupport f.val ∩ tsupport v.val:=  subset_inter tsupport_mul_subset_left tsupport_mul_subset_right
lemma support_arc {r : ℝ} (hr:0<r) : tsupport (eclipse K r).val ⊆ sun K r:= by
  apply closure_minimal _ (closed_sun K r); intro x hx; by_contra he; change ¬ (_≤_ ∧ _≤_) at he; change ((cutoff r (K.starProjection x):ℂ)-(cutoff (r/2) (K.starProjection x):ℂ))≠0 at hx
  rcases not_and_or.mp he with h|h
  · have h':= (not_le.mp h).le; rw [cutoff_eq_one (half_pos hr) h', cutoff_eq_one hr (h'.trans (half_le_self hr.le)),sub_self] at hx; contradiction
  have h':= (not_le.mp h).le; rw [cutoff_eq_zero hr h', cutoff_eq_zero (half_pos hr) (by linarith),sub_self] at hx; contradiction

def pinch (K : Submodule ℝ E) (r : ℝ) : E →L[ℝ] K:= r⁻¹ • K.orthogonalProjectionOnto
lemma pinched (r : ℝ) (x : E) : (pinch K r x).val=r⁻¹ • K.starProjection x:=rfl
lemma pinch_length {r : ℝ}(hr:0<r) (x:E) : ‖pinch K r x‖= ‖K.starProjection x‖/r:= by
   change ‖(pinch K r x).val‖=_; rw [pinched,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),div_eq_mul_inv,mul_comm]
lemma pinch_shell {r : ℝ}(hr:0<r) {x:E}: (pinch K r x).val∈ sun K 1 ↔ x∈ sun K r:=by
   change ‖K.starProjection (pinch K r x).val‖∈ Icc (1/2:ℝ) (2*1) ↔ _; rw [starProjection_eq_self_iff.mpr (pinch K r x).property]
   change (1/2:ℝ) ≤ ‖pinch K r x‖ ∧ ‖pinch K r x‖ ≤ 2*1 ↔ _≤_ ∧ _≤_; rw [pinch_length K hr,le_div_iff₀ hr,div_le_iff₀ hr, mul_one, show ((1/2:ℝ)*r)=r/2 by ring]
lemma pinch_normalizes {r : ℝ}{A : E≃L[ℝ] E} (h:Proper A r K) (hr : 0 < r) (x : E) : pinch K r (A x) = pinch K 1 x:= by
   apply Subtype.ext; rw [pinched, h.normal,pinched,inv_smul_smul₀ hr.ne',inv_one,one_smul]
lemma arc_shrinks {A : E≃L[ℝ] E} {r t : ℝ}(hr:0<r) (h:Proper A r K)(x:E) : (window K (r*t)).val (A x)= (window K t).val x:= by
    change (↑(cutoff _ _):ℂ)=(↑(cutoff _ _):ℂ); rw [h.normal]; unfold cutoff; rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,mul_pow,mul_pow,mul_div_mul_left _ _ (pow_ne_zero _ hr.ne')]
lemma arc_relabel {A : E≃L[ℝ] E}{r : ℝ}(hr:0<r)(h : Proper A r K)(x:E) : (eclipse K r).val (A x)= (eclipse K 1).val x:= by
   change (window K r).val (A x)-(window K (r/2)).val (A x)=_
   have he:=arc_shrinks K (t:=1) hr h x; rw [mul_one] at he; rw [← show r*(1/2:ℝ)=r/2 by ring,arc_shrinks K hr h x,he]; rfl

def dyad (n : ℕ) := ((1:ℝ)/2)^n
lemma dyad_zero : dyad 0=1:= rfl -- pow_zero rfl?
lemma dyad_pos (n : ℕ) : 0<dyad n:= pow_pos (by norm_num) n
lemma dyad_le (n : ℕ) : dyad n≤1:= pow_le_one₀ (by norm_num) (by norm_num) -- _
lemma dyad_next (n : ℕ) : dyad (n+1)=dyad n /2:= by unfold dyad; rw [pow_succ]; ring
lemma dyad_shrivels : Tendsto dyad atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
lemma split_to (n : ℕ) : ∑ i∈Finset.range n,eclipse K (dyad i)= window K 1-window K (dyad n):= by
  induction n with
  | zero=> simp [dyad_zero]
  | succ i h => rw [Finset.sum_range_succ,h,eclipse,dyad_next]; abel
lemma reunion (f : SmoothTests E) (hf : tsupport f.val ⊆ {x | ‖K.starProjection x‖ ≤ 1}) {x:E}(hx:K.starProjection x≠0):
      ∀ᶠ i in (atTop:Filter ℕ),( ∑ j∈Finset.range i, mask (eclipse K (dyad j)) f).val =ᶠ[𝓝 x] f.val:= by
     let r:= ‖K.starProjection x‖; have hr : 0< r:= norm_pos_iff.mpr hx
     have he:=dyad_shrivels.eventually (p:=fun t=> t<r/4) (gt_mem_nhds (div_pos hr (by norm_num)))
     filter_upwards [he] with i hi; filter_upwards [(K.starProjection.continuous.norm.tendsto x).eventually (lt_mem_nhds (show r/2 < ‖K.starProjection x‖ from half_lt_self hr))] with y hy
     rw [sum_test]; change ∑ j∈Finset.range i,(eclipse K (dyad j)).val y*f.val y = f.val y; rw [← Finset.sum_mul,← sum_test,split_to]; by_cases hh:f.val y=0; rw [hh,mul_zero]
     change ((cutoff 1 (K.starProjection y):ℂ)-(cutoff (dyad i) (K.starProjection y):ℂ)) * _ = _; rw [cutoff_eq_one zero_lt_one (hf (subset_closure (show y∈support f.val from hh))),cutoff_eq_zero (dyad_pos _) (by linarith),Complex.ofReal_one,Complex.ofReal_zero,sub_zero,one_mul]
end common
variable {k : ℕ} {g : Group k} {P : E→ₗᵢ[ℝ] Points k}(u : Fans P g) {r : ℝ}
namespace Fans
local notation "K!" => normalOn P g
local notation "o" => pinch K!
/-- Sector mask and its actual patch after rescaling. -/
def ray (q : Splittings g)(r : ℝ) : SmoothTests E := mask (eclipse K! r) ⟨(u.sector q).val ∘ o r, (infSmooth _).comp ((o r).contDiff)⟩
def patch (q : Splittings g) (r : ℝ) := sun K! r ∩ (o r ⁻¹' tsupport (u.sector q).val)
lemma ray_value (q : Splittings g) (t : ℝ) (x:E) : (u.ray q t).val x=(eclipse K! t).val x * (u.sector q).val (pinch (normalOn P g) t x):=rfl
lemma ray_closes (q : Splittings g)(r : ℝ) : IsClosed (u.patch q r) := (closed_sun _ _).inter ((isClosed_tsupport _).preimage (o r).continuous)
lemma ray_in (q : Splittings g){r : ℝ} (hr:0<r) : tsupport (u.ray q r).val ⊆ u.patch q r := (support_mask (eclipse K! _) _).trans (inter_subset_inter (support_arc _ hr) (support_comp (o r) (o r).continuous _))
lemma ray_sums (f : SmoothTests E){r : ℝ}(hr :0<r) : ∑ q:Splittings g, mask (u.ray q r) f = mask (eclipse K! r) f:= by
  apply Subtype.ext; funext x; rw [sum_test]; change ∑ q:Splittings g,((eclipse K! r).val x * (u.sector q).val (o r x))*f.val x=_; rw [← Finset.sum_mul, ← Finset.mul_sum]; by_cases he:x ∈ sun K! r; rw [u.covers _ ((pinch_shell _ hr).2 he),mul_one]; rfl
  change _= (eclipse K! r).val x*f.val x; rw [notMem_support.mp (show x∉ support (eclipse K! r).val from fun hm=>he (support_arc _ hr (subset_closure hm))),zero_mul]
lemma ray_tests (f : SmoothTests E) (hf : tsupport f.val ⊆ {x | ‖(normalOn P g).starProjection x‖ ≤ 1}) {x:E} (hx : (normalOn P g).starProjection x≠0) :
      ∀ᶠ i in (atTop : Filter ℕ), ( ∑ j∈Finset.range i, ∑ q:Splittings g, mask (u.ray q (dyad j)) f).val =ᶠ[𝓝 x] f.val:= by
    simp_rw [u.ray_sums _ (dyad_pos _)]; exact reunion _ _ hf hx
lemma ray_proper {A:E≃L[ℝ] E}(h : Proper A r K!)(hr:0<r)(q : Splittings g) : composed A (u.ray q r)= u.ray q 1 := by apply Subtype.ext; funext x; change (u.ray q r).val (A x)=_; rw [ray_value, ray_value,pinch_normalizes _ h hr,arc_relabel _ hr h]

variable (hp : plane g ≤ LinearMap.range P.toLinearMap) -- require explicit call, before all.
include hp
lemma ray_dist (x:E)(f h : Nails g)(r:ℝ) : centroid f.val (P (o r x).val)-centroid h.val (P (o r x).val) = r⁻¹ • (centroid f.val (P x)-centroid h.val (P x)) := by
   rw [pinched,map_smul,map_smul,map_smul,← smul_sub,← subgroup_from_center hp x f.property.1 f.property.2,← subgroup_from_center hp x h.property.1 h.property.2]; congr 1; abel
lemma through (q : Splittings g) (i j : q.val.parts)(h : i≠j) (f:Nails i.val)(f':Nails j.val) : ∃ c>(0:ℝ),∀ {r:ℝ}, 0<r → ∀ x∈u.patch q r,c*r ≤ ‖centroid f.val (P x)-centroid f'.val (P x)‖:=by
   obtain ⟨c,hc,he⟩:= margin P u q i j h f f'; refine ⟨c,hc,@fun r hr x hx=>?_⟩
   let y:=pinch (normalOn P g) r x; have hh:= he y.val y.property ((pinch_shell _ hr).2 hx.1) (by rw [orthogonalProjectionOnto_mem_subspace_eq_self]; exact hx.2); rw [show centroid f.val (P y.val)-centroid f'.val (P y.val) = r⁻¹ • (centroid f.val (P x)-centroid f'.val (P x)) from ray_dist (P:=P) hp x ⟨f.val,Finset.Subset.trans f.property.1 (q.val.le i.property), f.property.2⟩ ⟨f'.val, Finset.Subset.trans f'.property.1 (q.val.le j.property), f'.property.2⟩ r,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hr).le, mul_comm,← div_eq_mul_inv] at hh; exact (le_div_iff₀ hr).mp hh
lemma lights (q : Splittings g) (hr : 0<r) : u.patch q r ⊆ bright P q.val := fun x hx i j he f l=> by
    obtain ⟨t,ht,h⟩:= u.through hp q i j he f l; exact sub_ne_zero.mp (norm_pos_iff.mp ((mul_pos ht hr).trans_le (h hr _ hx)))
end Fans
omit [FiniteDimensional ℝ E] in
lemma bright_slots {R : Pieces g} {x:E} (hx : x∈ bright P R) (i : Group k)(hi : i ∈ R.parts) (j : Group k)(hj:j∈R.parts) (h : i≠j) (a : Fin k)(ha:a∈i)(b : Fin k)(hb : b∈ j) : (P x) a≠(P x) b := by
   have he := hx (⟨i,hi⟩:R.parts) ⟨j,hj⟩ (fun h'=> h (congr_arg Subtype.val h')) ⟨{a},Finset.singleton_subset_iff.mpr ha, Finset.singleton_nonempty _⟩ ⟨{b},Finset.singleton_subset_iff.mpr hb,Finset.singleton_nonempty _⟩; simpa only [centroid_single] using he
end YM.Contacts.Normal
