import YM.TraceExtension.ConeLaplace
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! Nonnegative moment Tauberian, part I: the tests separate compactified
forward-cone points. -/

set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension
open Function Set Filter MeasureTheory Measure Metric Mink Boundary
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace

abbrev Lid := OnePoint cone
abbrev Sensor := C(Lid,ℝ)

lemma lid_escape : Tendsto (Subtype.val : cone → E4) (coclosedCompact cone) (cocompact E4) := by
    rw [coclosedCompact_eq_cocompact]; exact Mink.closed_cone.isClosedEmbedding_subtypeVal.tendsto_cocompact
lemma lid_inner {u : E4} (hu : u ∈ inside) : Tendsto (fun p : cone => inner ℝ u p.val) (coclosedCompact cone) atTop := by
    let a := (time u-‖spatial u‖)
    have ha : 0<a := sub_pos.mpr hu
    have hx : ∀ p : cone, a/2*‖p.val‖ ≤ inner ℝ u p.val := by
        rintro ⟨p,hp⟩
        obtain ⟨ht,hm⟩ := (cone_self p).1 hp
        have hk : ‖spatial p‖≤time p := hp
        have he : ‖p‖≤2*time p := by unfold Mink.m at hm; nlinarith [Mink.squares p]
        have h := (abs_le.mp (abs_real_inner_le_norm (spatial u) (spatial p))).1
        dsimp only; rw [Mink.pairing]; dsimp only [a];
        dsimp only [a] at ha
        linarith [mul_le_mul_of_nonneg_left he ha.le,mul_le_mul_of_nonneg_left hk (norm_nonneg (spatial u))]
    exact tendsto_atTop_mono hx (Tendsto.const_mul_atTop (by positivity) (tendsto_norm_cocompact_atTop.comp lid_escape))

def sensor (u : inside) : Sensor :=
    OnePoint.continuousMapMk ⟨fun p:cone => ↑(lagWeight u p.val),
      (continuous_subtype_val.comp (lagWeight_cont _)).comp continuous_subtype_val⟩ 0
      (Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr (lid_inner u.property)))

@[simp] lemma sensor_at (u : inside) (p : cone) : sensor u (p : Lid) = Real.exp (-(inner ℝ u.val p.val)) := rfl

lemma add_inside {u v : E4} (hu : u ∈ inside) (hv : v ∈ inside) : u+v ∈ inside := by
    change ‖spatial _‖ < time _
    rw [Mink.clock_add,Mink.rest_add]; exact (norm_add_le ..).trans_lt (add_lt_add hu hv)

lemma clock_inside : basis timeAxis ∈ inside := by simp [inside]
def scanner := insert 1 (range sensor)

lemma scanner_mul (x y : Sensor) (hx : x∈scanner) (hy : y∈scanner) : x*y ∈ scanner := by
    rcases hx with h|⟨a,rfl⟩
    · rw [h,one_mul]; exact hy
    rcases hy with h|⟨b,rfl⟩
    · rw [h,mul_one]; exact Or.inr ⟨_, rfl⟩
    refine Or.inr ⟨⟨a.val+b.val,add_inside a.property b.property⟩,?_⟩
    ext p
    refine OnePoint.rec ?_ (fun x => ?_) p
    · change (0:ℝ)=0*0; ring
    simp [inner_add_left, Real.exp_add, mul_comm]

def scanAlg : Subalgebra ℝ Sensor := (Submodule.span ℝ scanner).toSubalgebra
    (Submodule.subset_span (Or.inl rfl : (1:Sensor) ∈ scanner)) fun x y hx hy => by
      induction hx using Submodule.span_induction with
      | mem z hz =>
        induction hy using Submodule.span_induction with
        | mem w hw => exact Submodule.subset_span (scanner_mul z w hz hw)
        | zero => rw [mul_zero]; exact Submodule.zero_mem _
        | add w v _ _ hw hv => rw [mul_add]; exact Submodule.add_mem _ hw hv
        | smul a w hw ih => rw [mul_smul_comm]; exact Submodule.smul_mem _ a ih
      | zero => rw [zero_mul]; exact Submodule.zero_mem _
      | add z w _ _ hz hw => rw [add_mul]; exact Submodule.add_mem _ hz hw
      | smul a z hz ih => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a ih

lemma open_separates (p q : E4) (hs : ∀ u ∈ inside, inner ℝ u p = inner ℝ u q) : p=q := by
    let b := basis timeAxis
    apply ext_inner_left ℝ
    intro x
    have he := (show Continuous (fun t : ℝ => b+t • x) from by fun_prop).tendsto 0
    simp only [zero_smul,add_zero] at he
    obtain ⟨t,ht,hp⟩ := (((he.mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))).eventually
      (Mink.open_inside.mem_nhds clock_inside)).and self_mem_nhdsWithin).exists
    have h := hs (b+t • x) ht; simp only [inner_add_left, real_inner_smul_left,hs b clock_inside] at h
    exact mul_left_cancel₀ (show t ≠ 0 from (show 0<t from hp).ne') (add_left_cancel h)

open scoped OnePoint in
lemma energy_separates (x y : Lid) (h : x≠y) : ∃ u, sensor u x ≠ sensor u y := by
    induction x using OnePoint.rec <;> induction y using OnePoint.rec
    · contradiction
    · exact ⟨⟨_,clock_inside⟩, (Real.exp_pos _).ne⟩
    · exact ⟨⟨_,clock_inside⟩,(Real.exp_pos _).ne'⟩
    rename_i p q
    by_contra! ht
    apply h; congr 1; apply Subtype.ext; apply open_separates; intro u hu
    have he := ht ⟨u,hu⟩; simpa using he

lemma scan_separates : scanAlg.SeparatesPoints := by
    intro x y h
    obtain ⟨u,hu⟩ := energy_separates x y h
    exact ⟨sensor u,⟨sensor u,Submodule.subset_span (show sensor u∈scanner from Or.inr ⟨_,rfl⟩),rfl⟩, hu⟩

lemma scan_dense (x : Sensor) {ε : ℝ} (he : 0<ε) : ∃ f ∈ (Submodule.span ℝ scanner), ‖f-x‖<ε := by
    obtain ⟨v,h⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints _ scan_separates x ε he
    exact ⟨v.val,v.property,h⟩
end YM.TraceExtension
