import YM.Extra.SOURCE_HISTORIES.Delays
import YM.Extra.SOURCE_HISTORIES.Replay


/-!
# Pre-L currency (and numeric thresholds for a ONE-schedule consumer)

Plain obligations on numeric knobs. This is not RRequirements (no
assertion of the *analytic* estimates based on these gates nor of ability
to combine them with other vacuum, Ward etc gates). . We allow
requiring local errors in both directions ≤ L^-0.4 in the paid conventions
(after the local producer's additional L and coupling delays); this leaves
room for orientation averaging and for assembly reserve L^-0.375. All such
comparisons at fixed stage/weight. Issue Bank & roomCost on the purchased
trajectory, not anew after picking an Order. Can use still bigger L. The
C_j socket must be earned before L, using all needed k and support
allocations of the SAME instance. E.g. numerical solvability in isolation
of `Plans` is NOT derivation of all these estimates simultaneously.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories.Doors
open Lattice Wilson RG Supply Source Function Filter Set MeasureTheory Bid Labels Motion Next.Foundations
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge}

/-- Exact one optional realization of the Buys rate under L minima. -/
def rate (L : Side) := (L.val:ℝ) ^ (-(2/5 : ℝ))
lemma rate_pos (L : Side) : 0<rate L := by unfold rate; positivity

lemma pre_tilt (s T : ℝ) : ∃ k : ℕ, ∀ L : Side, k ≤ L.val →
    rate L * s ≤ 1 ∧ rate L * (1+s) * T ≤ barunit L := by
  have he (u : ℝ) (hu : 0 < u) (C : ℝ) : ∀ᶠ n : ℕ in atTop, ((n:ℝ)^(-u)) * C ≤ 1 := by
    have hv := ((tendsto_rpow_neg_atTop hu).comp tendsto_natCast_atTop_atTop).mul_const C
    rw [zero_mul] at hv; exact hv.eventually (ge_mem_nhds zero_lt_one)
  have ha : 0 < (2/5:ℝ) - 3/8 := by norm_num
  obtain ⟨k,hk⟩ := eventually_atTop.mp ((he (2/5) (by norm_num) s).and (he (2/5-3/8) ha ((1+s)*T)))
  refine ⟨k,fun L hL => ⟨(hk _ hL).1,?_⟩⟩
  let x := (L.val:ℝ)
  have hx : 0 < x := by unfold x; positivity
  have hp : barunit L = x ^ (-(3/8:ℝ)) := by
    unfold barunit puffs
    change (x^((1:ℝ)/8))⁻¹^(3:ℕ)=_
    rw [← Real.rpow_neg hx.le, ← Real.rpow_mul_natCast hx.le (-(1/8:ℝ)) 3]; norm_num
  rw [hp]
  calc
    rate L * (1+s) * T = (x ^ (-((2/5:ℝ)-3/8)) * ((1+s)*T)) * x ^ (-(3/8:ℝ)) := by
      rw [mul_right_comm (x ^ (-((2/5:ℝ)-3/8))),← Real.rpow_add hx,show (-((2/5:ℝ)-3/8))+ -(3/8:ℝ) = -(2/5) by ring]
      unfold rate x; ring
    _ ≤ 1*(x ^ (-(3/8:ℝ))) := mul_le_mul_of_nonneg_right (hk _ hL).2 (by positivity)
    _ = _ := one_mul _

/-- Numerical-only Knobs on this Sheet. Can strengthen ratios, k, P,
or exp, but then still have to pay these exact obligations on new Sheet. -/
structure Plans (P : Sheet G) (C : ℕ → ℝ) (W : Worth) : Prop where
  origin j : 1 ≤ C j
  grown j : j ≤ (P.profile j).order ∧ j ≤ (P.profile j).power
  share j : price G (max (P.profile j).order (P.profile j).power) ≤ (P.profile j).columns
  motion j d : d ≤ j → (C j+1)*orbitCost ((frames G).level d) ≤ W.K j
  columns j : 64*(W.K (j+1))^2 ≤ (P.profile j).columns

/-- All currency on purchased levels. -/
structure Budget (K : Levels G) (C : ℕ → ℝ) (W : Worth) : Prop where
  stage m : K.clock.J m ≤ (K.params m).order ∧ K.clock.J m ≤ (K.params m).power
  sectionBudget m : price G (max (K.params m).order (K.params m).power) ≤ (K.params m).columns
  sequences m d : d ≤ K.clock.J m → Latch G d K m
  room : roomCost K W
  bank : Bank W K
  fits (H : History G) : H.levels=K → ∀ m d, d ≤ K.clock.J m →
    Buys H ((frames G).level d) W m (C (K.clock.J (m+1))) (rate (K.S.block m))

/-- Both floors issued against the anticipated profile/neighbor costs,
independent of actual L/periods. -/
theorem afford (P : Sheet G) (C : ℕ → ℝ) (W : Worth) (h : Plans P C W) :
    ∃ n : ℕ → ℕ, ∃ b : ℕ → ℝ, ∀ v : ℕ → ℕ, n ≤ v → ∀ D : Rolls { P with floorL := v }, ∀ M : Levels G,
      M.clock.factor=D.L → M.clock.stage=P.profile → (∀ m, b (M.clock.J (m+1)) ≤ M.clock.hatBeta m) →
      Budget M C W := by
  obtain ⟨k,hk⟩ := Bid.buffer W P h.columns
  obtain ⟨b,hb⟩ := entrances P
  choose u hu using fun j d : ℕ => pre_tilt (P.profile j).columns (orbitCost ((frames G).level d))
  let N (j) := max (k j) ((Finset.range (j+1)).sup (u j))
  refine ⟨N,b, fun v hv D K hf hs he => ?_⟩
  obtain ⟨hB,hC⟩ := hk v (fun j => le_trans (le_max_left ..) (hv j)) D K hf hs
  have hd (m) : K.params m=P.profile (K.clock.J m) := by unfold Levels.params Calendar.params; rw [hs]
  refine ⟨fun m => (hd m).symm ▸ h.grown _,fun m => (hd m).symm ▸ h.share _,fun m d hg => hb K hs he d m hg,hC,hB,?_⟩
  rintro H rfl m d hg
  let j := H.levels.clock.J (m+1)
  let L := H.S.block m
  have hj : d≤j := hg.trans (H.levels.fits.mono m.le_succ)
  have hz : u j d ≤ (D.L j).val := (show u j d ≤ N j from le_trans
    (Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))) (le_max_right ..)).trans
      ((hv j).trans (D.large j).need)
  have hL : L=D.L j := (H.levels.fits.sameFactor m).symm.trans (congr_fun hf j)
  have hu := hu j d L (hL.symm ▸ hz)
  constructor
  · exact h.origin _
  · exact (rate_pos _).le
  · rw [hd]; exact hu.2
  rw [hd]; exact (mul_le_mul_of_nonneg_right (add_le_add_right hu.1 _) (zero_le_one.trans (orbitCost_one_le _))).trans
    (h.motion j d hj)

/-- Not needed as an input, just tests the `Plans` NUMERIC scope. When
allocating actual plans do such maxima before L and don't assert other
contexts still hold after profile changes. Keep exact grown profiles here if
already chosen, anticipated costs `C` must still suffice. -/
theorem alone (P : Sheet G) (C : ℕ → ℝ) (h : ∀ j, 1 ≤ C j)
    (ht : ∀ j, j ≤ (P.profile j).order ∧ j ≤ (P.profile j).power) :
    ∃ u : ℕ → Stage, ∃ Q : Sheet G, Q.kernel=P.kernel ∧ Q.floorL=P.floorL ∧ Q.first=P.first ∧
      Q.profile=u ∧ (∀ j, (P.profile j).columns ≤ (u j).columns ∧ u j = {P.profile j with
        columns := (u j).columns,columns_ge := (u j).columns_ge}) ∧ ∃ W, Plans Q C W := by
  let g j d := (C j+1)*orbitCost ((frames G).level d)
  have hx j d : 0≤g j d := mul_nonneg (by linarith only [h j]) (zero_le_one.trans (orbitCost_one_le _))
  let v j := ∑ d ∈ Finset.range (j+1),g j d
  have he j : 0 ≤ v j := Finset.sum_nonneg fun d _ => hx j d
  let W : Worth := {
    K := fun k => 1+∑ j∈Finset.range (k+1),v j
    prices := fun k => le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => he j)
    growth := monotone_nat_of_le_succ fun k => by
      change 1 + ∑ j∈Finset.range (k+1),v j ≤ 1 + ∑ j∈Finset.range (k+1+1),v j
      rw [Finset.sum_range_succ _ (k+1)]; linarith only [he (k+1)] }
  let u j : Stage := {
    P.profile j with
      columns := max (P.profile j).columns
        (max (price G (max (P.profile j).order (P.profile j).power)) (64*(W.K (j+1))^2))
      columns_ge := le_trans (P.profile j).columns_ge (le_max_left ..) }
  let Q : Sheet G := {P with profile := u}
  refine ⟨u,Q,rfl,rfl,rfl,rfl,fun j => ⟨le_max_left ..,rfl⟩,W,⟨h,ht,fun j =>
    (le_max_left ..).trans (le_max_right ..), fun j d hi => ?_,fun j => (le_max_right ..).trans (le_max_right ..)⟩⟩
  have hh : g j d ≤ v j := Finset.single_le_sum (fun i _ => hx j i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  have hu : v j ≤ ∑ i∈Finset.range (j+1),v i := Finset.single_le_sum (fun i _ => he i) (by simp)
  exact hh.trans (hu.trans (le_add_of_nonneg_left zero_le_one))

end YM.Extra.Histories.Doors
