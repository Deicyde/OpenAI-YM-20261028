import YM.Bid.Fuels
import YM.Corona.Spend

/-!
# Ticket geometry for the centered link tiling

`m` is the level giving the *physical side*
of the replication cell; the stop `i` may be later. Keep alignment even down
to `m`; pay for pairwise spacing only from `i` to cutoff. This only concerns
the positions: no assertion of a marker trajectory or cylinder estimates.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.I03
open Lattice Cells Stock Mix

-- Ratio counts compose since they realize exact subdivision of positive side
-- lengths. No need to lift into an arbitrary no-wrap domain: the canonical
-- lift (including even-side ties) scales under these embeddings.
private lemma embed_comp {a b c : Side} (p : Ratio a b) (q : Ratio b c)
    (r : Ratio a c) (x : Site a) :
    q.embed (p.embed x) = r.embed x := by
  have hr : r.count.val = q.count.val * p.count.val := by
    apply (Nat.mul_right_inj a.property.ne').mp
    calc
      _ = c.val := r.exact_size.symm
      _ = b.val * q.count.val := q.exact_size
      _ = a.val * p.count.val * q.count.val := congr_arg (· * q.count.val) p.exact_size
      _ = _ := (Nat.mul_assoc ..).trans
        (congr_arg (a.val * ·) (Nat.mul_comm p.count.val q.count.val))
  rw [Ratio.embed, p.lift_embed, Ratio.embed, smul_smul, hr]

/-- The camps really use the centered roots of each history step, not just
some children with the indicated parent. -/
theorem camp_step {G : Gauge} (C : Family G) (p : ℕ) {m j : ℕ} (hj : m ≤ j)
    (x : Site (C.side m p)) :
    (C.path.levels.clock.op j p).ratio.embed (camp C p m j x) =
      camp C p m (j+1) x := by
  simp only [camp, dif_pos hj, dif_pos (hj.trans (Nat.le_succ j))]
  exact embed_comp _ _ _ _

theorem answer : YM.Bid.I03 := by
  intro G C k hk ht m i ho N _ p hN
  refine ⟨fun v => ?_, ?_, fun r hir _ x y hxy => ?_⟩
  · rw [copy_home, camp, dif_pos hN, zero_add]
  · intro j hj _ v
    rw [← camp_step C p hj, Ratio.embed_parent]
  · obtain ⟨hm, he⟩ := Tabs.open_later _ _ ht ho hir (zero_le_one.trans hk)
    -- Distinct replication sites before embedding: torus separation ≥ 1.
    have hs : 1 ≤ separation x y :=
      Nat.pos_of_ne_zero fun H => hxy <|
        (Corona.line_home x y).symm.trans (Corona.line_end x y H.le)
    let Q := C.S.toDepth hm p
    have hu : Q.count.val ≤ separation (Q.embed x) (Q.embed y) :=
      (le_mul_of_one_le_right (Nat.zero_le _) hs).trans (Corona.below Q x y)
    simp only [camp, dif_pos hm]
    calc
      _ = k * (C.path.levels.clock.coverSize r : ℝ)^2 := mul_comm ..
      _ ≤ C.S.a m / C.S.a r := he
      _ = (Q.count.val : ℝ) := (div_eq_iff (C.S.a_pos _).ne').mpr
        ((C.S.embeds_scale Q).symm.trans (mul_comm ..))
      _ ≤ (separation (Q.embed x) (Q.embed y) : ℝ) := by exact_mod_cast hu
end YM.Work.I03
