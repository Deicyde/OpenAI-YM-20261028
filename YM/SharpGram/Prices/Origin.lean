import YM.OPE.Columns.SectorCost
import YM.ProofPorts.GRID_RENEWED_RESERVES.Speeds
/-!
# Sharp full-space *forward-to-reference* transmission

No symmetric claim about inverse and no grade-annihilating restriction in this
lemma. Isolate the exact most-relevant direction (unit). On all others
engineering separation by at least one power, so even after *all* distortion
in the leading matrix and all error leaked back to the unit, for enough step
credit the unit still dominates. `roomCost, Bank` which are already carried
in `Triangle`'s applications are ample. Unlike `Columns.whole_origin`, after
paying the exact engineering growth there is NO subpower remaining. Uniform
in admissible pair of scales (even growing with cutoff) and all cutoff
and period choices. Argument uses the enhancement mechanism (charge separately
and exactly on grade) already applicable for the unit to `Triangle`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram
open Function Set Filter Lattice RG Wilson Labels Source Work.G08 Bid Extra.Histories MergeProof
open Push.Local OPE OPE.Columns Next.UVStress
open scoped Topology BigOperators
variable {G : Gauge} {d : ℕ} (F : Labels.Frame G d)
set_option quotPrecheck false
local notation "μ" => F.coeffSize
lemma plusCore (x : F.Coeff) : μ x = μ (F.core x) + μ (x 0 • F.e0) := by
  unfold Frame.coeffSize
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j=0 <;> simp [Frame.core, Frame.e0,h]

lemma gapSize (x : F.Coeff) (L : Side) :
    μ (vowel F L (F.core x)) ≤ (L.val:ℝ) ^ (d-1) * μ (F.core x) := by
  unfold Frame.coeffSize
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  simp only [vowel,norm_mul,norm_pow,Complex.norm_natCast]
  rcases eq_or_ne j 0 with h|h
  · simp [h,Frame.core]
  refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by exact_mod_cast L.pos) ?_) (norm_nonneg _)
  exact Nat.sub_le_sub_left (GridRenewal.Speed.grade_grows j h) d

lemma unitOnlySize (v : ℂ) (L : Side) (U : Heading F) :
    μ (U.leads L (v • F.e0)) = (L.val:ℝ)^d * μ (v • F.e0) := by
  have he : U.leads L F.e0 = (L.val:ℂ)^d • F.e0 := by
    change U.map (vowel F L F.e0) = _
    rw [show vowel F L F.e0 = _ from ?_, map_smul, U.unit]
    ext i
    by_cases h : i = 0
    · subst i
      simp [vowel, Frame.zero_degree]
    simp [vowel,Frame.e0,h]
  rw [map_smul,he,Size.smul, Size.smul, Size.smul, norm_pow,Complex.norm_natCast]
  ring

variable {F} {x y : F.Coeff → F.Coeff} {H : History G} {W : Worth} {m : ℕ}
  (hc : roomCost H.levels W) (hb : Bank W H.levels)

include hc hb
set_option quotPrecheck false
local notation "L" => H.S.block m
local notation "K" => W.K (H.levels.clock.J (m+1))
lemma chargedWithin : 0 ≤ barunit L ∧ barunit L ≤ 1 ∧ 1 + K ≤ ((L).val:ℝ) := by
  let l := L
  have hk : 1 ≤ K := W.prices _
  let a : ℝ := (l.val:ℝ)
  have ha : 1 ≤ a := by unfold a; exact_mod_cast l.property
  let e := barunit l
  have he : 0 ≤ e ∧ e ≤ 1 := by
    have hx := OPE.Columns.ε_small hb (i:=m); have hv := (H.levels.params (m+1)).columns_ge
    refine ⟨hx.1, ?_⟩
    calc
      e ≤ 2*K*barunit l := le_mul_of_one_le_left hx.1 (by linarith only [hk])
      _ ≤ _ := le_mul_of_one_le_right (show 0 ≤ 2*K*barunit l from mul_nonneg (by linarith only [hk]) hx.1) (by linarith only [hv])
      _ ≤ 1 := hx.2
  have hh : 1 + K ≤ a := by
    have hK : (64:ℝ)*K^2 ≤ (H.levels.params (m+1)).columns := OPE.Columns.room hc _ _ (Nat.le_add_right ..)
    have hL : (H.levels.params (m+1)).columns ≤ a := OPE.Columns.column_small hb
    nlinarith only [hK,hL,hk]
  exact ⟨he.1,he.2,hh⟩

lemma oneBlockCost (n : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    K * ((((L).val:ℝ)^n)*w) + barunit L * w ≤ ((L).val:ℝ)^(n+1) * w := by
  obtain ⟨he,he',hh⟩ := chargedWithin (m:=m) hc hb
  let a : ℝ := ((L).val:ℝ)
  have ha : 1 ≤ a := by unfold a; exact_mod_cast (L).property
  calc
    _ ≤ K*(a^n*w) + a^n*w := add_le_add le_rfl (mul_le_mul_of_nonneg_right (he'.trans (one_le_pow₀ ha)) hw)
    _ = (1+K)*(a^n*w) := by ring
    _ ≤ a*(a^n*w) := mul_le_mul_of_nonneg_right hh (by positivity)
    _ = _ := by rw [pow_succ', mul_assoc]

lemma unitDominates (h : Triangle H W m x y) (v : F.Coeff) :
    μ (y v) ≤ ((L).val:ℝ)^d * μ (x v) := by
  obtain ⟨T,hT,hQ,herr⟩ := h.leads
  let w := μ (F.core (x v))
  let l := L
  have hk : 1 ≤ K := W.prices _
  let a : ℝ := (l.val:ℝ)
  let e := barunit l
  have hw : 0 ≤ w := size_nonneg ..
  have hop : μ (T.leads L (F.core (x v))) ≤ K*(a^(d-1)*w) :=
    ((hQ (vowel F L _)).1).trans (mul_le_mul_of_nonneg_left (gapSize F ..) (zero_le_one.trans hk))
  have gain : K*(a^(d-1)*w) + e*w ≤ a^d*w := by
    rcases eq_or_ne d 0 with h|h
    · have hg (i:F.Index) : i=0:= by
        by_contra hh; have hp := GridRenewal.Speed.grade_grows i hh; have ht := F.bound i; omega
      rw [show w=0 from ?_]
      · simp
      have hg : F.core (x v) = 0 := by
        funext i; rw [hg i]; simp [Frame.core]
      unfold w; simp [hg,Frame.coeffSize]
    exact (oneBlockCost (m:=m) hc hb (d-1) hw).trans_eq
      (by rw [Nat.sub_add_cancel]; omega)
  have hz : μ (T.leads L (x v)) ≤ μ (T.leads L (F.core (x v))) + a^d * μ ((x v) 0 • F.e0) := by
    rw [show T.leads L (x v) = T.leads L (F.core (x v)) + T.leads L ((x v) 0 • F.e0) from
      ((congr_arg _ ((Size.core_plus F _).symm)).trans (map_add ..))]
    exact (Size.add ..).trans_eq (congr_arg (μ (T.leads L (F.core (x v))) + ·) (unitOnlySize ..))
  calc
    _ ≤ (μ (T.leads L (x v)) + μ (y v - T.leads L (x v))) := size_triangle F (y v) _
    _ ≤ μ (T.leads L (F.core (x v))) + a^d * μ ((x v) 0 • F.e0) + e*w := add_le_add hz (herr v)
    _ ≤ a^d * w + a^d * μ ((x v) 0 • F.e0) := by linarith only [hop,gain]
    _ = _ := by rw [plusCore F (x v),mul_add]

section all
omit hc hb
variable {C : Family G} {k j N p : ℕ} {r D}
lemma passPrice {d k j N p : ℕ}
    (T : TableTickets C W r D)
    (x : C.label d) (hr : C.ref d ≤ k) (hk : k ≤ j) (hn : j ≤ N) :
    quota C d k N p x ≤ (C.S.a k / C.S.a j)^d * quota C d j N p x := by
  induction hk using Nat.decreasingInduction with
  | self => rw [div_self (C.S.a_pos j).ne', one_pow, one_mul]
  | of_succ i hi ih =>
    have hv := (C.S.a_pos j)
    specialize ih (hr.trans (Nat.le_succ i))
    calc
      _ ≤ ((C.S.block i).val:ℝ)^d * quota C d (i+1) N p x := unitDominates
          T.system.costs.cost T.system.costs.back (T.columns d N p ((hr.trans hi.le).trans hn) i hr (hi.trans_le hn)) _
      _ ≤ ((C.S.block i).val:ℝ)^d * _ := mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by rw [show C.S.a i = ((C.S.block i).val:ℝ)*C.S.a (i+1) from ?_,mul_div_assoc,mul_pow, ←mul_assoc]
                  rw [Schedule.a_step, mul_div_cancel₀ _ (by positivity)]
end all
end YM.SharpGram
