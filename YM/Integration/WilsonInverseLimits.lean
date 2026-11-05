import YM.RG08.Apex.Rest

/-! The native row-limit argument at an arbitrary positive decay exponent.
This retains the actual rate rather than replacing the inverse supplier's
1/104 by the unrelated 1/4 rate of the older specialized lemma. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInverseSchedule
open RG08
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function
open Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths
open Work.F08 Push.AbsoluteSums UVExtension.Free
open RG08 RG08.Wings
open scoped BigOperators Topology Real Classical
variable {I : Type}

/-- The row-limit argument works at every positive rate, including the
unaltered `1/104` provided by the inverse-map supplier.  The constants are
chosen before the window index and cutoff within the given family. -/
theorem rowLimitData {S : Chain} {u : I → Windows}
    {α β : ℕ → Type} [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    {F : ∀ (_ : ℕ) (i : ℕ), Row (α i) (β i)} {σ : ℕ → ℝ} {t : ℕ}
    {ρ : ℝ} (hρ : 0 < ρ) (hσ : ∀ i, 0 < σ i)
    (h : RowBoth (menu (u := u) S) (chop S ρ)
      (fun i : Wings u t => F i.N i.i) (fun i => F i.M i.i)
      (fun i => σ i.i)) :
    ∃ (A B : ℝ) (p q : ℕ), 0 ≤ A ∧ 0 ≤ B ∧
      ∀ s : Wings u t,
        Received (fun n => F n s.i) (apex (fun n => F n s.i))
          (σ s.i) (A * (s.menu S) ^ p) ∧
        ∀ N ≥ s.i + t,
          (F N s.i - apex (fun n => F n s.i)).strip (σ s.i)
            (B * (s.menu S) ^ q * gain S.S ρ s.i N) := by
  obtain ⟨_, ⟨A, p, hA, H⟩, hx⟩ := h.fresh
  obtain ⟨_, ⟨B, q, hB, H'⟩, hv⟩ := h.moves
  refine ⟨A, B, p, q, hA, hB, fun s => ?_⟩
  have hh (N : ℕ) (hN : s.i + t ≤ N) :
      (F N s.i).strip (σ s.i) (A * (s.menu S) ^ p) :=
    strip_mono (hx {s with N := N, M := N, cut := hN, side := le_rfl})
      le_rfl (by rw [Pi.one_apply, mul_one]; exact (H _).2)
  obtain ⟨f, hf, rate⟩ := cauchy_row_rate (X := fun n => F n s.i)
    (fun n => B * (s.menu S) ^ q * gain S.S ρ s.i n) (hσ _)
    ((eventually_ge_atTop _).mono hh)
    (fun N hN M hM =>
      strip_mono (hv {s with N := N, M := M, side := hM, cut := hN})
        le_rfl (mul_le_mul_of_nonneg_right (H' _).2 (gain_pos ..).le))
    (by simpa using (tendsto_gain S.S hρ s.i).const_mul (B * (s.menu S) ^ q))
  rw [tendsto_nhds_unique (apex_win ⟨f, hf.entries⟩) hf.entries]
  exact ⟨hf, rate⟩

theorem rowLimitRate {S : Chain} {u : I → Windows}
    {α β : ℕ → Type} [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    {F : ∀ (_ : ℕ) (i : ℕ), Row (α i) (β i)} {σ : ℕ → ℝ} {t : ℕ}
    {ρ : ℝ} (hρ : 0 < ρ) (hσ : ∀ i, 0 < σ i)
    (h : RowBoth (menu (u := u) S) (chop S ρ)
      (fun i : Wings u t => F i.N i.i) (fun i => F i.M i.i)
      (fun i => σ i.i)) :
    RowBoth (menu (u := u) S) (chop S ρ)
      (fun i : Wings u t => F i.N i.i)
      (fun i => apex (fun n => F n i.i)) (fun i => σ i.i) := by
  obtain ⟨A, B, p, q, hA, hB, data⟩ := rowLimitData hρ hσ h
  let V := menu (u := u) (r := t) S
  have powers (n : ℕ) : Weighed V (V ^ n) :=
    Weighed.power V (Wings.sh S) n
  refine ⟨h.fresh, ⟨_, (Weighed.constant V hA).times (powers p), ?_⟩,
    ⟨_, (Weighed.constant V hB).times (powers q), ?_⟩⟩
  · intro i
    rw [Pi.mul_apply, Pi.pow_apply, Pi.one_apply, mul_one]
    exact (data i).1.bound
  · intro i
    rw [Pi.mul_apply, Pi.pow_apply]
    exact (data i).2 i.N i.cut

end YM.Integration.WilsonInverseSchedule
