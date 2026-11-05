import Mathlib.Analysis.Normed.Group.Tannery
import YM.Bid.Kitchen


/-!
# Fixed-period continuity of forced gathering

For the all-address `deviation` cost we may sum the weighted hit bounds over the
finite native torus (not a volume-independent estimate). In each solid the
field-dependent predicate and the finite label set are exactly the same at the
two parameter values being compared.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.H04
open Filter Function Set RG Wilson Lattice Shoot Ovens Ovens.Pipes
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {n : Side} {X : Pipes G n} {S : ℝ → Tap G n} {T : Set ℝ} {P : BudgetPoint}

lemma summable_packets (F : ℕ ≃ X.Pellet) {c : Label → ℝ} {γ : ℝ}
    (hc : ∀ i, 0 ≤ c i) (hH : Ac.Hit X.patch P.B c (P.supportExponent + 1) γ)
    (hp : (P.B + P.B + 1 : ℕ)^4*(γ:ℝ) ≤ 1) (hγ : 0 ≤ γ) :
    Summable fun i => P.mass (addr F P i).support (∏ j∈(F i).val, c j) := by
  let r := Ac.roots X.patch P.B c P.supportExponent
  have h (x : Site n) : SumBudget (r x) (Real.exp γ - 1) :=
    Ac.forest X.patch P.B P.exponent_pos.le hc hH hp hγ x
  have hs (x : Site n) : Summable fun i => r x (F i).val :=
    (h x).2.1.comp_injective (show Injective (fun i : ℕ => (F i).val) from
      Subtype.val_injective.comp F.injective)
  refine Summable.of_nonneg_of_le (f := fun i => ∑ x : Site n, r x (F i).val) ?_ ?_
    (summable_sum fun x _ => hs x)
  · intro i
    exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun j _ => hc j)
  intro i
  obtain ⟨x, hx⟩ := (X.plot_ne (F i)).mono (X.plot_sub (F i))
  have hroot : Ac.Spark X.patch (F i).val ∧ x ∈ (F i).val.biUnion X.patch :=
    ⟨(F i).property.2.1,hx⟩
  change Real.exp (P.supportExponent * (coverNumber P.B ((F i).val.biUnion X.patch) : ℝ)) * _ ≤ _
  have he : r x (F i).val ≤ ∑ y : Site n, r y (F i).val :=
    Finset.single_le_sum (fun y _ => (h y).1 _) (Finset.mem_univ x)
  simpa only [r, Ac.roots, if_pos hroot] using he

lemma reach_bound {c : Label → ℝ} {κ : ℝ}
    (hc : ∀ i, 0 ≤ c i) (hκ : 0 ≤ κ) (hd : ∀ a ∈ T, ∀ i : Label, ∀ U,
      |reach (S a) i U| ≤ i.elim (fun _ => Real.exp (-κ)) (fun _ => 1)*c i) :
    ∀ a ∈ T, ∀ i U, ‖reach (S a) i U‖ ≤ c i := by
  intro a ha i U
  exact (hd a ha i U).trans (mul_le_of_le_one_left (hc i) (by
    rcases i with i|i
    · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hκ)
    · exact le_rfl))

lemma prod_bound {c : Label → ℝ} (hd : ∀ a ∈ T, ∀ i U, ‖reach (S a) i U‖ ≤ c i)
    {a : ℝ} (ha : a ∈ T) (s : Finset Label) (U : Config G n) :
    ‖∏ j∈s, reach (S a) j U‖ ≤ ∏ j∈s, c j := by
  rw [norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => hd a ha j U)

lemma solid_bound {c : Label → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hd : ∀ a ∈ T, ∀ i U, ‖reach (S a) i U‖ ≤ c i)
    (F : ℕ ≃ X.Pellet) {a : ℝ} (ha : a ∈ T) (i : ℕ) (U : Config G n) :
    ‖solid F P (S a) i U‖ ≤ ∏ j∈(F i).val, c j := by
  unfold solid; split
  · exact prod_bound hd ha _ U
  · rw [norm_zero]; exact Finset.prod_nonneg fun j _ => hc j

lemma prod_varies {c : Label → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hd : ∀ a ∈ T, ∀ i U, ‖reach (S a) i U‖ ≤ c i) (hj : invariantJet P S T)
    {a : ℝ} (ha : a ∈ T) (s : Finset Label) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ b in 𝓝[T] a, ∀ U,
      ‖(∏ j∈s, reach (S a) j U) - ∏ j∈s, reach (S b) j U‖ ≤ ε := by
  induction s using Finset.induction_on with
  | empty =>
    intro ε he
    filter_upwards with b U
    simpa using he.le
  | @insert j s hjs hi =>
    intro ε he
    let v := ∏ j∈s, c j
    have hv : 0 ≤ v := Finset.prod_nonneg fun k _ => hc k
    let δ := ε / (1+c j+v)
    have hz : 0 < (1+c j+v) := by linarith [hc j]
    have hδ : 0 < δ := div_pos he hz
    filter_upwards [self_mem_nhdsWithin, hi δ hδ, hj a ha j δ hδ] with b hb hp hq U
    rw [Finset.prod_insert hjs, Finset.prod_insert hjs]
    let x := reach (S a) j U; let y := reach (S b) j U
    let u := ∏ k∈s, reach (S a) k U; let w := ∏ k∈s, reach (S b) k U
    have hy : ‖x-y‖ ≤ δ := by rw [norm_sub_rev]; exact hq U
    calc
      ‖x*u - y*w‖ = ‖x*(u-w) + (x-y)*w‖ := by ring_nf
      _ ≤ ‖x*(u-w)‖ + ‖(x-y)*w‖ := norm_add_le ..
      _ ≤ c j * δ + δ*v := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul (hd _ ha j U) (hp U) (norm_nonneg _) (hc j))
          (mul_le_mul hy (prod_bound hd hb s U) (norm_nonneg _) hδ.le)
      _ ≤ (1+c j+v)*δ := by nlinarith only [hδ]
      _ = ε := by unfold δ; field_simp

lemma solid_varies {c : Label → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hd : ∀ a ∈ T, ∀ i U, ‖reach (S a) i U‖ ≤ c i) (hj : invariantJet P S T)
    (F : ℕ ≃ X.Pellet) {a : ℝ} (ha : a ∈ T) (i : ℕ) (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ b in 𝓝[T] a, ∀ U, ‖solid F P (S a) i U-solid F P (S b) i U‖ ≤ ε := by
  filter_upwards [prod_varies hc hd hj ha (F i).val ε he] with b hb U
  unfold solid; split
  · exact hb U
  · simpa using he.le

lemma earned_retakes (F : ℕ ≃ X.Pellet) (hj : invariantJet P S T) (hl : X.little P S T) :
    retakes F P S T := by
  obtain ⟨κ, γ, c, hp, hγ, hκ, hc, hrc, hH⟩ := hl
  have hd := reach_bound hc hκ hrc
  intro a ha ε he
  let r := fun i => ∏ j∈(F i).val, c j
  let u := fun b i U => ‖solid F P (S a) i U - solid F P (S b) i U‖
  let g := fun b i => sSup (Set.range (u b i))
  have hg (b) (hb : b ∈ T) (i : ℕ) :
      (0 ≤ g b i ∧ ∀ U, u b i U ≤ g b i) ∧ g b i ≤ r i + r i := by
    have hr : ∀ y∈Set.range (u b i), y ≤ r i + r i := by
      rintro _ ⟨U,rfl⟩
      exact (norm_sub_le ..).trans <| add_le_add (solid_bound hc hd F ha i U) (solid_bound hc hd F hb i U)
    have hu (U) : u b i U ≤ g b i := le_csSup ⟨_,hr⟩ (mem_range_self _)
    exact ⟨⟨(norm_nonneg _).trans (hu 1),hu⟩,csSup_le (range_nonempty _) hr⟩
  let m := fun b i => P.mass (addr F P i).support (g b i)
  let l := fun i => P.mass (addr F P i).support (r i)
  have hl := summable_packets F hc hH hp hγ
  have hs : Summable (fun i => l i + l i) := hl.add hl
  have hle (b) (hb : b ∈ T) i : 0 ≤ m b i ∧ m b i ≤ l i + l i := by
    dsimp only [m, l, BudgetPoint.mass]
    rw [← mul_add]
    exact ⟨mul_nonneg (Real.exp_pos _).le (hg b hb i).1.1,
      mul_le_mul_of_nonneg_left (hg b hb i).2 (Real.exp_pos _).le⟩
  have ht (i) : Tendsto (fun b => g b i) (𝓝[T] a) (𝓝 0) := by
    refine tendsto_order.mpr ⟨?_,?_⟩
    · intro z hz
      filter_upwards [self_mem_nhdsWithin] with b hb
      exact hz.trans_le (hg b hb i).1.1
    intro z hz
    filter_upwards [solid_varies hc hd hj F ha i (z/2) (half_pos hz)] with b hb
    refine lt_of_le_of_lt (csSup_le (range_nonempty _) ?_) (half_lt_self hz)
    rintro _ ⟨U,rfl⟩; exact hb U
  have hm (i) : Tendsto (fun b => m b i) (𝓝[T] a) (𝓝 0) := by
    simpa [m, BudgetPoint.mass] using (ht i).const_mul (Real.exp (P.supportExponent *
      (coverNumber P.B (addr F P i).support : ℝ)))
  have hsum : Tendsto (fun b => ∑' i, m b i) (𝓝[T] a) (𝓝 0) := by
    have hub : ∀ᶠ b in 𝓝[T] a, ∀ i, ‖m b i‖ ≤ l i + l i := by
      filter_upwards [self_mem_nhdsWithin] with b hb i
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hle b hb i).1] using (hle b hb i).2
    simpa using (tendsto_tsum_of_dominated_convergence hs hm hub)
  filter_upwards [self_mem_nhdsWithin, (tendsto_order.mp hsum).2 ε he] with b hb hs'
  refine ⟨g b, fun i => (hg b hb i).1.1, fun U i => (hg b hb i).1.2 U,
    fun i => (hle b hb i).1, hs.of_nonneg_of_le (fun i => (hle b hb i).1) (fun i => (hle b hb i).2), hs'.le⟩

theorem answer : YM.Bid.H04 := by
  intro G n X S F T R A P h hj hl
  refine ⟨h.beta, h.v, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun ε he a ha => ?_⟩
  filter_upwards [h.continuous ε he a ha, earned_retakes F hj hl a ha ε he] with b h₁ h₂
  obtain ⟨c, _, hc, _, hE, _⟩ := h₁
  obtain ⟨g,hg,hu,hm⟩ := h₂
  exact ⟨c, g, hc, fun i => ⟨hg i, fun U => hu U i⟩, hE, hm⟩
end YM.Work.H04
