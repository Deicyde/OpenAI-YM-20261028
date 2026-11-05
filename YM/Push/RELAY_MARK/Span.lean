import YM.Push.RELAY_MARK.Current

/-!
# Enough microscopic directions even with avoidance

No change of probe arities or Taylor variables. Gives actual
finite linear combinations (members of span) for use making
section functions of the links, from linearized large-cover analysis.
One for the degree-j equation factor, a different one, leaving any
one prescribed link independent, for other factors. Annihilator
arguments are only in the finite real Taylor test space.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set Filter MeasureTheory Wilson Lattice RG Source Source.Drops Work.G03 Labels InnerProductSpace
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {j d : ℕ}

structure Point where
  w : Walk
  e : Edge Cover
  lands : stop 0 w=e.1
  open_path : avoids 0 w e

/-- Positive `field` component, before t-slot scaling. -/
def positiveLinear (H : Hol G) (d : ℕ) (b : Point) (i : G.ColorIndex) : Snap G d →ₗ[ℝ] ℝ :=
  ((EuclideanSpace.proj i) ∘L linearForce H d b.w b.e.2).toLinearMap

def mounted (H : Hol G) (d : ℕ) := Submodule.span ℝ (Set.range (fun p : Point × G.ColorIndex => positiveLinear H d p.1 p.2))

lemma force_span (H : Hol G) (hp : Peg H (j+2)) (Q : Taylor G j →ₗ[ℝ] ℝ)
    (he : ∀ x ∈ LinearMap.range Maxwell.gaugeJet, Q x=0) :
    Q ∘ₗ (LinearMap.proj (φ:=fun k : Fin ((j+2)-1) => Taylor G k.val) ⟨j,by omega⟩) ∈ mounted H (j+2) := by
  suffices hv : _ ∈ (mounted H (j+2)).dualCoannihilator.dualAnnihilator by
    rwa [Subspace.dualCoannihilator_dualAnnihilator_eq] at hv
  refine (Submodule.mem_dualAnnihilator _).mpr (fun x hx => he _ (force_kernel_last H j hp x ?_))
  intro e w h h'
  ext i
  exact (Submodule.mem_dualCoannihilator _).mp hx (positiveLinear H (j+2) ⟨w,e,h,h'⟩ i)
    (Submodule.subset_span ⟨(⟨w,e,h,h'⟩,i),rfl⟩)

/- Delete an arbitrary finite set of evaluation points from curvature-jet sampling. -/
private lemma detours {x : E4} {X : Set Cover} (h : X.Finite) (hx : x ≠ 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,index t x∉X := by
  have hi (z : X) : ∀ᶠ t : ℝ in 𝓝[>] 0,index t x≠(z:Cover) := by
    have hv (v : E4) : Tendsto (fun t : ℝ => t • v) (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_id.mono_left (nhdsWithin_le_nhds (s:=Ioi 0) (a:=(0:ℝ)))).smul_const v
    have ha := ((shrink_grid x).sub (hv (castPos z))).eventually (isOpen_ne.mem_nhds (by simpa using hx))
    filter_upwards [ha] with t ht he
    simp [he] at ht
  haveI := h.to_subtype
  filter_upwards [eventually_all.mpr hi] with t ht h
  exact ht ⟨_,h⟩ rfl

-- `h` only on x outside deleted set for each axis pair.
private lemma safe_top (A : Jet G) (k : ℕ)
    (h : ∀ i j : Axis, i < j → ∃ X : Set Cover, X.Finite ∧ ∀ x : Cover, x∉X →
      ∑ l ∈ Finset.range (k+1), net (A l) i j (castPos x) 1 = 0) : A k=0 := by
  refine zero_of_zero_partials _ (fun i j x hij => ?_)
  obtain ⟨Y, hy, h⟩ := h i j hij
  let f (p : E4 × ℝ) := ∑ l ∈ Finset.range (k+1), p.2^(k-l) • net (A l) i j p.1 p.2
  have he (t : ℝ) (y : Cover) (hh : y∉Y) : f (t • castPos y, t) = 0 := calc
    _ = ∑ l ∈ Finset.range (k+1), t^k • net (A l) i j (castPos y) 1 := by
      unfold f; apply Finset.sum_congr rfl
      intro l hl; rw [scale_net, smul_smul, ← pow_add, Nat.sub_add_cancel (Nat.le_of_lt_succ (Finset.mem_range.mp hl))]
    _ = 0 := by rw [← Finset.smul_sum, h y hh, smul_zero]
  have hx (x : E4) : f (x,0) = net (A k) i j x 0 := by
    unfold f
    rw [Finset.sum_range_succ, Finset.sum_eq_zero]
    · simp
    intro l hl; rw [zero_pow (Nat.sub_ne_zero_of_lt (Finset.mem_range.mp hl)), zero_smul]
  have hc : Continuous f := continuous_finsetSum _ fun _ _ => (continuous_snd.pow _).smul (continuous_net ..)
  rw [← hx]
  have ha (z : E4) (hz : z ≠ 0) : f (z,0)=0 := by
    have ht : Tendsto (fun t : ℝ => f (t • castPos (index t z),t)) (𝓝[>] 0) (𝓝 (f (z,0))) :=
      (hc.tendsto _).comp ((shrink_grid z).prodMk_nhds (tendsto_id.mono_left nhdsWithin_le_nhds))
    exact tendsto_nhds_unique_of_eventuallyEq ht tendsto_const_nhds ((detours hy hz).mono (fun t ht => he t _ ht))
  by_cases h0 : x=0
  · subst x
    have ht (t : ℝ) (ht : 0<t) : t • basis 0≠0 := smul_ne_zero ht.ne' (by
      intro he; have := congr_arg (fun u : E4 => u (0 : Axis)) he; simp at this)
    have hh : Tendsto (fun t : ℝ => f (t • basis 0,0)) (𝓝[>] 0) (𝓝 (f (0,0))) := by
      have hb : Tendsto (fun t : ℝ => t • basis 0) (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id (x:=𝓝 (0:ℝ))).smul_const (basis (0:Axis))
      exact ((hc.tendsto _).comp (hb.prodMk_nhds tendsto_const_nhds)).mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique_of_eventuallyEq hh tendsto_const_nhds (eventually_nhdsWithin_of_forall fun t h => ha _ (ht t h))
  exact ha x h0

private lemma safe_all (A : Jet G) (k : ℕ)
    (h : ∀ i j : Axis, i < j → ∃ X : Set Cover, X.Finite ∧ ∀ x : Cover, x∉X →
      ∑ l ∈ Finset.range k, net (A l) i j (castPos x) 1 = 0) : ∀ l < k, A l=0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hv := safe_top A k h
    intro l hl
    obtain hl|rfl := (Nat.le_of_lt_succ hl).lt_or_eq
    · apply ih ?_ l hl
      simpa only [Finset.sum_range_succ,hv,net_zero, add_zero] using h
    exact hv

private lemma safe_check (H : Hol G) (hp : Peg H d) (b : Edge Cover) (A : Snap G d)
    (h : ∀ s : Slot, safe b s → Blurb H d s A = 0) : A=0 := by
  have he := safe_all (expand d A) (d-1) (fun i j hij => by
    let p : PlaqAxes := ⟨(i,j),hij⟩
    refine ⟨_,finite_exception b p,fun x hx => ?_⟩
    obtain ⟨s,Hs,ho,hr⟩ := safe_slot b x p (of_not_not hx)
    have hc := h s Hs; rw [hp.initial,samples, hr,ho] at hc; exact hc)
  funext ⟨i,hi⟩; simpa only [expand,dif_pos hi, Pi.zero_apply] using he i hi

def safeLinear (H : Hol G) (d : ℕ) (s : Slot) (i : G.ColorIndex) : Snap G d →ₗ[ℝ] ℝ :=
    ((EuclideanSpace.proj i) ∘L Blurb H d s).toLinearMap

lemma safe_span (H : Hol G) (hp : Peg H d) (b : Edge Cover) (Q : Snap G d →ₗ[ℝ] ℝ) :
    Q ∈ Submodule.span ℝ (Set.range (fun p : ({s : Slot // safe b s}) × G.ColorIndex => safeLinear H d p.1.val p.2)) := by
  let W := Submodule.span ℝ (Set.range (fun p : ({s : Slot // safe b s}) × G.ColorIndex => safeLinear H d p.1.val p.2))
  change Q ∈ W
  suffices hv : Q ∈ W.dualCoannihilator.dualAnnihilator by rwa [Subspace.dualCoannihilator_dualAnnihilator_eq] at hv
  refine (Submodule.mem_dualAnnihilator _).mpr (fun x hx => ?_)
  have he := safe_check H hp b x (fun s hs => by
    ext i
    exact (Submodule.mem_dualCoannihilator _).mp hx (safeLinear H d s i) (Submodule.subset_span ⟨(⟨s,hs⟩,i),rfl⟩))
  rw [he,map_zero]
end YM.Push.Mark
