import YM.FullVolume.Connect

/-! Euclidean path price & multidir Taylor remainder on compact
coordinate sets away from TORUS coincidence (cover convention). Use all
mesh here, then pull to an already admitted mesh sequence without another
extraction. Last proof price uses two further derivatives; order unrestricted
for every fixed derivative at every admitted p. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Function Set Filter Metric MeasureTheory Lattice RG Wilson Extraction Extraction.Lease Difference Gaps Cells
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {n:ℕ}{G:Gauge}{C:Family G}
lemma nohitOpen (S:Schedule) (p n): IsOpen (NoHit S p n):=by
  rw [show NoHit S p n= ⋂ i:Fin n, ⋂ j:Fin n,⋂ _:i≠j, ⋃ a : Axis, {x:Points n | ¬ periodic S p (x i a) (x j a)} by ext; simp [NoHit]]
  exact isOpen_iInter_of_finite (fun i=>isOpen_iInter_of_finite (fun j=>isOpen_iInter_of_finite (fun _=>isOpen_iUnion (fun a=>not_tie_open ..))))

def stretch (v:MotionIndex n→ℂ) : Points n→L[ℝ] ℂ := LinearMap.toContinuousLinearMap
    { toFun x := ∑ a:MotionIndex n, x a.1 a.2 • v a
      map_add' x y:= by simp_rw [PiLp.add_apply, add_smul]; exact Finset.sum_add_distrib
      map_smul' r x:=by simp_rw [PiLp.smul_apply,smul_eq_mul, mul_smul]; exact (Finset.smul_sum ..).symm }
lemma loyal (v:MotionIndex n→ℂ) (b : MotionIndex n) : stretch v (Dir b)=v b:=by
  change ∑ i : MotionIndex n, Dir b i.1 i.2 • v i=v b
  rw [Finset.sum_eq_single b]; unfold Dir; simp [Points.direction,basis]
  · rintro ⟨x,y⟩ _ hv; obtain ⟨j,k⟩:=b
    by_cases hx:x=j <;> by_cases hy:y=k <;> simp_all [Dir,Points.direction,basis,PiLp.single_apply]
  simp
lemma stretching {ι : Type*}{T:Filter ι}{v:ι→MotionIndex n→ℂ}{a: MotionIndex n→ℂ} (h : ∀ j,Tendsto (fun k=> v k j) T (𝓝 (a j))) : Tendsto (fun i=> stretch (v i)) T (𝓝 (stretch a)):=by
  apply Extra.WeakScaling.norm_fit_deriv
  intro i; simpa only [show Points.direction i.1 i.2= Dir i from rfl,loyal] using! h i -- simplify target

namespace FixedBounds
variable (h:FixedBounds C)(v:Fin n→C.book.Token)(l:List (MotionIndex n)) (p:ℕ)
include h

lemma confines {K:Set (Points n)} (hk : K ⊆ NoHit C.S p n) (he:IsCompact K) :
    ∃ B:ℝ,0≤B ∧ ∀ᶠ N in atTop,∀ x:Positions n,tag (C.S.a N) x∈ K→ ‖gKernel C v l N p x‖ ≤ B:=by
  obtain ⟨r,hr,hR⟩:=Gaps.some C.S p he hk
  obtain ⟨b,hb,H⟩:=h.bounds n v l r hr
  refine ⟨b,hb,H.mono fun i hi x hx=> hi p x (fun u w hu=> gridSeparation C.S _ rfl (hR _ hx) _ _ hu.symm)⟩

lemma localLip {K:Set (Points n)} (hk: K ⊆ NoHit C.S p n) (he:IsCompact K) :
    ∃ r B : ℝ, 0 < r ∧ 0 ≤ B ∧ ∀ᶠ N in atTop,∀ x y:Positions n,
      tag (C.S.a N) x∈K → dist (tag (C.S.a N) y) (tag (C.S.a N) x) ≤ r →
        dist (gKernel C v l N p y) (gKernel C v l N p x) ≤ B * dist (tag (C.S.a N) y) (tag (C.S.a N) x):=by
  obtain ⟨r,hr,hT⟩ := he.exists_cthickening_subset_open (nohitOpen C.S p n) hk
  choose f hf hF using fun j:MotionIndex n=> confines h v (j::l) p hT he.cthickening
  obtain ⟨b,hb,hB⟩:= ((eventually_ge_atTop (0:ℝ)).and (eventually_all.mpr fun j=>eventually_ge_atTop (f j))).exists
  refine ⟨r,b*Fintype.card (MotionIndex n),hr,mul_nonneg hb (Nat.cast_nonneg _),?_⟩
  filter_upwards [eventually_all.mpr hF] with i hi x y hx hy
  let t:= C.S.a i; let F:= gKernel C v l i p
  refine stroll (C.S.a_pos _) F _ _ _ _ hb hy (fun u j hu=> ?_)
  rw [dist_eq_norm,unique_units F (C.S.a_pos _) j u,norm_smul, Real.norm_of_nonneg (C.S.a_pos _).le]
  exact mul_le_mul_of_nonneg_left ((hi j u (mem_cthickening_of_dist_le _ _ _ _ hx hu)).trans (hB j)) (C.S.a_pos _).le

/-- Uniform Taylor inequality away from coincidence. Last derivative needed
for this form even on plateau are FULL-precision paid, not a tilt cost. -/
theorem taylor {K:Set (Points n)} (hk : K ⊆ NoHit C.S p n) (he:IsCompact K):
    ∃ B r:ℝ, 0 ≤ B ∧ 0 < r ∧ ∀ᶠ N in atTop, let t:= C.S.a N; let f:=gKernel C v l N p; let P:= fun j x=> gKernel C v (j::l) N p x
      ∀ x y:Positions n, tag t x∈K → dist (tag t y) (tag t x)≤r →
        ‖f y-f x-stretch (fun j=> P j x) (tag t y-tag t x)‖ ≤ B*(dist (tag t y) (tag t x))^2:=by
  choose r b hr hb hR using fun j:MotionIndex n=> localLip h v (j::l) p hk he
  obtain ⟨A,hA,hB⟩:= ((eventually_ge_atTop (0:ℝ)).and (eventually_all.mpr fun i=> eventually_ge_atTop (b i))).exists
  obtain ⟨s,hs,hS⟩:= ((show ∀ᶠ s:ℝ in 𝓝[>] 0, 0<s from self_mem_nhdsWithin).and (eventually_all.mpr fun i=> eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds (hr i)))).exists
  refine ⟨A*Fintype.card (MotionIndex n),s,mul_nonneg hA (Nat.cast_nonneg _),hs,?_⟩
  filter_upwards [eventually_all.mpr hR] with i hi t f P x y hx hy
  let d:= dist (tag t y) (tag t x); have hd : 0 ≤ d:= dist_nonneg
  let p:= stretch (fun j=>P j x)
  let w u:= f u - p (tag t u)
  have he (u : Positions n) (j : MotionIndex n) : w (u+drive j) - w u=t • (P j u-P j x):=by
    unfold w; rw [sub_sub_sub_comm, unique_units f (C.S.a_pos _) j u, tagged,map_add,map_smul, add_sub_cancel_left,smul_sub]
    unfold p; rw [loyal]; rfl
  have hz:=stroll (C.S.a_pos _) w x y d (A*d) (mul_nonneg hA hd) le_rfl (fun u s hu=> ?_)
  · rw [dist_eq_norm (w y)] at hz; unfold w at hz; rw [sub_sub_sub_comm,← map_sub p] at hz; exact hz.trans_eq (by unfold d; ring)
  have hU:=hi s x u hx (hu.trans (hy.trans (hS _)))
  rw [dist_eq_norm,he,norm_smul, Real.norm_of_nonneg (C.S.a_pos _).le, ← dist_eq_norm]
  refine mul_le_mul_of_nonneg_left (hU.trans (mul_le_mul (hB s) hu dist_nonneg hA)) (C.S.a_pos _).le
end FixedBounds
end YM.FullVolume
