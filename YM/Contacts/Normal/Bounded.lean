import YM.Contacts.Normal.Rays
/-!
# Uniform scale changes during one root pairing

Families of tests with controlled relative compacts across the step. Support changing only through
the colliding block (to *at most* the strip for the fixed/running-length extension). No estimate
uses a smaller fixed collar tied to the parent radius when the smaller relative coordinates can
reach the subtraction strip.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Normal
open Function Filter Set Metric MeasureTheory Submodule
open scoped Topology BigOperators Classical ContDiff InnerProductSpace
variable {E : Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable (K : Submodule ℝ E) {L : Submodule ℝ E} {x y : E} {A : E≃L[ℝ] E} {R r s u B : ℝ}
lemma projected_bounded (x:E) : ‖K.starProjection x‖≤‖x‖:=by exact K.norm_starProjection_apply_le x
abbrev strip (s:ℝ) := {x:E| ‖K.starProjection x‖ ≤ s}
def halo (s : ℝ)(t : Bool)(U : Set E) := if t then U ∪ ((slide K 0 ⁻¹' U) ∩ strip K (2*s)) else U
lemma ordinary (t : Bool) (U : Set E) : U ⊆ halo K s t U:=by cases t; rfl; exact Set.subset_union_left
lemma strip_closes : IsClosed (strip K s):= isClosed_le K.starProjection.continuous.norm continuous_const
lemma halo_closes {X : Set E}(h : IsClosed X)(t : Bool) : IsClosed (halo K s t X):= by cases t; exact h; exact h.union ((h.preimage (slide K 0).continuous) |>.inter (strip_closes K))
lemma tail_hug {t : Bool} {U : Set E}(hx : U ⊆ strip K B)(hb:2*s≤ B) : halo K s t U ⊆ strip K B:=by cases t; exact hx; exact Set.union_subset hx fun x h=> h.2.trans hb
-- associated passing points
lemma relative_change (x : E) : x-slide K 0 x∈ K:=by rw [slide_zero,sub_sub_cancel]; exact K.starProjection_apply_mem _
lemma follows {U : Set E} {t : Bool} (hx : x ∈ halo K s t U): ∃ z∈U, x-z∈ K ∧ (x=z ∨ t=true):= by
   cases t; exact ⟨x,hx,by rw [sub_self]; exact K.zero_mem,Or.inl rfl⟩
   rcases (show _ ∨ _∧_ from hx) with h|h
   · exact ⟨x,h,by rw [sub_self]; exact K.zero_mem,Or.inl rfl⟩
   exact ⟨_,h.1,relative_change K x,Or.inr rfl⟩
lemma outside_row (h : x-y∈ L) (he : L≤ Kᗮ) : K.starProjection x=K.starProjection y:= by apply sub_eq_zero.mp; rw [← map_sub]; exact K.starProjection_apply_eq_zero_iff.mpr (he h)
lemma inherit_halo {U : Set E} (h : L ≤ Kᗮ)(v : Bool) (hx : U ⊆ strip K B): halo L s v U⊆ strip K B:=by intro x hu; obtain ⟨y,hy,hy',hh⟩:= follows _ hu; exact Eq.trans_le (congr_arg norm (outside_row K hy' h)) (hx hy) -- Eq.trans_le name?
lemma inherit_strip (he : L ≤ K) : strip K B ⊆ strip L B:= fun x h=> by change ‖L.starProjection x‖≤B; rw [← show L.starProjection (K.starProjection x)=L.starProjection x from absorb_projection he x]; exact (projected_bounded _ _).trans h
-- all enlarged sets tested at scale r; live always still only U
lemma test_halo (s:ℝ)(hs:0<s)(v:SmoothTests E)(m:ℕ){U:Set E} (hv : tsupport v.val ⊆ U): tsupport (deviation K s m v).val⊆ halo K s true U := by
   let T:= tsupport (taylor K s m v).val
   refine ( (?_ : tsupport (deviation K s m v).val ⊆ tsupport v.val ∪ T)).trans (union_subset_union hv ((taylor_support K hs m v).trans (inter_subset_inter (Set.preimage_mono hv) (by rfl))))
   refine closure_minimal ?_ ((isClosed_tsupport _).union (isClosed_tsupport _)); intro x h; by_cases he:v.val x=0
   · refine Or.inr (subset_closure ?_); change (taylor K s m v).val x≠0; intro hx; exact h (show v.val x-(taylor K s m v).val x=0 by rw [hx,he,sub_zero])
   exact Or.inl (subset_closure he)

/- General scale cost. `Fits A B` measures only geometry (Readers have separate apertures). -/
def limited (A : E≃L[ℝ] E)(B : ℝ) := A.symm ⁻¹' closedBall (0:E) B
omit [FiniteDimensional ℝ E] in
lemma limit_iff : x ∈ limited A B ↔ ‖A.symm x‖ ≤ B:= by simp [limited]
omit [FiniteDimensional ℝ E] in
lemma limited_mono (h : B ≤ s) : limited A B ⊆ limited A s:= preimage_mono (closedBall_subset_closedBall h)
lemma limit_compact : IsCompact (limited A B):=  A.symm.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall (0:E) B)
lemma rel_limit (h : Proper A R K)(hr : 0<R) : limited A B ⊆ strip K (R*B):=by
   intro x hx; obtain ⟨x,rfl⟩:= A.surjective x; refine ( ( ?_ : ‖K.starProjection (A x)‖=R*‖K.starProjection x‖)).trans_le ((mul_le_mul_of_nonneg_left ((projected_bounded ..).trans ?_) hr.le)) -- see parsing
   · rw [h.normal x,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
   have he:= limit_iff.mp hx; rwa [A.symm_apply_apply] at he

def relaunch (A:E≃L[ℝ] E)(r R:ℝ)(hr:0<r)(hp:0<R) := (resize K (r/R) (div_pos hr hp).ne').trans A
lemma launched (h : Proper A R K)(hr:0<r)(hp:0<R) : Proper (relaunch K A r R hr hp) r K:=by
   have hk:= (h.grant (r/R) ((div_pos hr hp).ne')) ; rw [mul_div_cancel₀ _ hp.ne'] at hk; exact hk -- guess
lemma launch_before (h : Proper A R K) (hr:0<r) (hp:0<R) (x:E) : A (slide K 0 x) = slide K 0 (relaunch K A r R hr hp x):= by
   rw [relaunch,ContinuousLinearEquiv.trans_apply,resizing,← h.commute,slip_inspect,zero_mul]
lemma farther {t : Bool} {U : Set E}(h : U ⊆ limited A B)(he : Proper A R K)(hr:0<r)(hp:0<R): halo K s t U ∩ sun K r ⊆ limited (relaunch K A r R hr hp) (2+B):= by
   intro x hx; let V:= relaunch K A r R hr hp; obtain ⟨x,rfl⟩:= V.surjective x; rw [limit_iff,show relaunch K A r R hr hp=V from rfl,V.symm_apply_apply]; obtain ⟨y,hy,hy',_⟩:= follows _ hx.1;
   have hN : ‖K.starProjection x‖≤2:= by
      have hh : ‖K.starProjection (V x)‖≤2*r:= hx.2.2; rw [(launched K he hr hp).normal x,norm_smul,Real.norm_eq_abs,abs_of_pos hr] at hh; exact le_of_mul_le_mul_left (hh.trans_eq (mul_comm _ _)) hr
   have hz : A (Kᗮ.starProjection x)=Kᗮ.starProjection y:= by
      have hi (x : E): slide K 0 x= Kᗮ.starProjection x:= by rw [foot,zero_smul,zero_add]
      rw [← hi, ← hi, launch_before K he hr hp x]; apply sub_eq_zero.mp; rw [← map_sub]; exact (slip_mem K 0 hy').trans (zero_smul ..)
   have hu:= he.commute 0 (A.symm y); simp_rw [foot,zero_smul,zero_add] at hu; rw [A.apply_symm_apply] at hu
   nth_rw 1 [← K.starProjection_add_starProjection_orthogonal x]; exact (norm_add_le ..).trans (add_le_add hN ((congr_arg norm (A.injective (hz.trans hu.symm))).trans_le ((projected_bounded ..).trans (limit_iff.mp (h hy))))) -- finish
end YM.Contacts.Normal
