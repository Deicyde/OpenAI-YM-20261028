import YM.Bid.Phase

set_option autoImplicit false
noncomputable section
namespace YM.Work.B11
open Set Filter Function OS OS.Ground Table Word
open scoped Topology NNReal

variable {G : Gauge} {L : Register G} {S : Table L}

private lemma carried_spaced {w : L.Word} {r : ℝ} (s : E4) (hs : spaced r (positions w)) :
    spaced r (positions (carry w s)) := by
  let e := finCongr (by simp [carry] : (carry w s).length = w.length)
  have ht (i) : positions (carry w s) i = positions w (e i) + s := by
    simp [positions, carry, e]
    rfl
  intro i j hij
  rw [ht, ht, cubedist, WithLp.ofLp_add, WithLp.ofLp_add, dist_add_right]
  exact hs _ _ (e.injective.ne hij)

private lemma realized_spaced {n : ℕ} {r : ℝ} {x : Points n} (v : Fin n → L.Token)
    (hs : spaced r x) : spaced r (positions (realize v x)) := by
  let e := finCongr (by simp [realize] : (realize v x).length = n)
  have ht (i) : positions (realize v x) i = x (e i) := by
    simp [positions, realize, e]
    rfl
  intro i j hij
  rw [ht, ht]; exact hs _ _ (e.injective.ne hij)

/-- Translation into a slab with unit padding at each side, even at zero arity. -/
private lemma packed {w : L.Word} {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) (hs : spaced r (positions w)) :
    ∃ (s : E4) (d : ℝ≥0), Slab timeAxis d (carry w s) ∧ buffer timeAxis r d (carry w s) := by
  obtain ⟨u,d,H⟩ := Spread.Resolution.place_exists (show distinct w from spaced_conf hr hs)
  have he : raised timeAxis 1 (carry w u) = carry w (u + basis timeAxis) := by simp [raised]
  have hv := swelling (fills H 1) 1
  rw [he] at hv
  refine ⟨_,_,hv,carried_spaced _ hs,?_⟩
  rw [← he]
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  have hq₀ := H.2.1.2 q hq
  have hq₁ := H.2.2 q hq
  push_cast
  simp
  constructor <;> linarith

private lemma slot_norm {V : Chamber S timeAxis} (A : Spread V) {w : L.Word} {d : ℝ≥0}
    (H : Slab timeAxis d w) : ‖A.slot w d H‖ ≤ ‖A.place d w‖ := by
  change ‖A.atom w d‖ ≤ _
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x =>
    (V.D.norm_orthogonalProjectionOnto_apply_le _).trans ((A.place d w).le_opNorm x.val)

private lemma char_norm {V : Chamber S timeAxis} {A : Spread V} (P : Spread.Resolution A) (i : P.X)
    (x : A.algebra) : ‖P.character i x‖ ≤ ‖x‖ := by
  haveI : IsClosed (A.algebra : Set V.VacuumOp) := isClosed_closure
  exact NonUnitalStarAlgHom.norm_apply_le (P.character i) x

/-- Whole-word zeroth-order estimate, uniform even over receiving tables and arity,
as long as the raw tokens obey the degree and norm bounds. -/
theorem phase_cap {V : Chamber S timeAxis} {A : Spread V} (P : Spread.Resolution A)
    (h : A.AllCopy) (D : ℕ) (R : ℝ) : ∃ C : ℝ, ∃ B : ℕ, 0 < C ∧
    ∀ (i : P.X) (T : Table L), P.receives T i → ∀ w : L.Word, constrained D R w →
    ∀ r : ℝ, 0 < r → r ≤ 1 → spaced r (positions w) → ‖T.expect w‖ ≤ Spread.radius C B w r := by
  obtain ⟨C,B,hC,H⟩ := h D R
  refine ⟨C,B,hC,fun i T hp w hw r hr hr' hs => ?_⟩
  obtain ⟨s,d,h₁,h₂⟩ := packed hr hr' hs
  have hc : constrained D R (carry w s) := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact hw q hq
  rw [hp w (spaced_conf hr hs) s d h₁]
  exact (char_norm ..).trans ((slot_norm A h₁).trans (by
    simpa [Spread.radius, carry] using H (carry w s) d hc h₁ r hr hr' h₂))

theorem answer : YM.Bid.B11 := by
  intro G C S V A P X _ h _ p H i n d v
  let t : Fin n → C.book.Token := fun j => ⟨d j,v j⟩
  obtain ⟨D,hD⟩ : ∃ D, ∀ j, d j ≤ D := (eventually_all.mpr fun j => eventually_ge_atTop (d j)).exists
  obtain ⟨R,hR⟩ : ∃ R, ∀ j, ‖v j‖ ≤ R := (eventually_all.mpr fun j => eventually_ge_atTop ‖v j‖).exists
  obtain ⟨K,B,hK,hb⟩ := phase_cap P h D R
  refine ⟨B*n,K^n*(n:ℝ)^(B*n),by positivity,fun r hr hr' x hs => ?_⟩
  have hw : constrained D R (realize t x) := by
    intro u hu
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hu
    exact ⟨hD j,hR j⟩
  have he := hb i (p i) (H.threads i) _ hw r hr hr' (realized_spaced t hs)
  rwa [Table.readAt, show (p i).read x t = _ from (p i).read_eq x d v,
    Spread.radius, show (realize t x).length = n from List.length_ofFn, div_eq_mul_inv,
    mul_pow, ← mul_assoc] at he

end YM.Work.B11
