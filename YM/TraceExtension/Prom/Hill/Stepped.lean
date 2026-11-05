import YM.Next.RANK.Stepped
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Coordinates
import YM.TraceExtension.Prom.Hill.Memorandum
import YM.TraceExtension.Prom.Hill.Station
/-!
  Variant of YM.Next.RANK.Stepped for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Perch
open Lattice Wilson RG Value Dock Station Peak Cells Read Marker Glyph Filter Set Extraction
open scoped Topology BigOperators Classical

variable {G : Gauge} {n : Side} {P : Rep G n} {A : Type*} [DecidableEq A] [Fintype A]
variable (C : Demand)

-- step tests specialized to THIS one path and collection of markers, uniform post-L constants.

-- K steps pay all height positions. actual β on history below k may differ from restarted.

variable {F : Family G} {m k N p v : ℕ} {b : ℝ}

-- step bound at fixed v specialized to one arc.
section
variable {q : Era} (Y : Course F N p k) (P : (u : ℕ) → Rep G (F.side u p))
variable (b : ℝ) (X : Points v) (m : ℕ) (hN : k ≤ N)

def ExhibitsSky (U : Config G (F.side N p) → veil (Fin v)) (q : Era) : Prop :=
    let A := F.path.levels
    let ℓ := middleSky A b k
    let s := A.clock.hatBeta k
    let S := Array.stamp (Ship.yardSky F b hN p) (F.beta N p) U
    let d := fun _ : (Ship.yardSky F b hN p).Cell × Fin v => Ship.allowance A m k
    ∀ j, widthSky A b k ≤ j → ∀ H : j<ℓ,
      let i : j+1 ≤ N := (show j+1 ≤ ℓ from H).trans ((beforeSky A b k).trans hN)
      let u := A.clock.hatBeta (j+1)
      let C := Y.flow S (j+1) i
      let p₀ := readersSky (C:=F) (b:=b) (p:=p) X hN i
      let p₁ := readersSky (C:=F) (b:=b) (p:=p) X hN ((Nat.le_succ j).trans i)
      let z := spouse s q (ℓ-(j+1))
      Notice (P (j+1)) p₀ C d q.coast.e z (z*w u) →
        Notice (P j) p₁ ((A.clock.op j p).push (Y.changeβ (j+1)) C) d q.coast.e (q.α*z+Perch.bill (1/2) s*z^2) (Perch.gas q.coast u)

def settledSky (q : Era) (u : Config G (F.side N p) → veil (Fin v)) {i : ℕ} (hi : i ≤ middleSky F.path.levels b k) : Prop :=
    let A := F.path.levels
    let j : i ≤ N := hi.trans ((beforeSky A b k).trans hN)
    let p₀ := readersSky (C:=F) (b:=b) (p:=p) X hN j
    let s := spouse (A.clock.hatBeta k) q (middleSky A b k - i)
    Value.Notice (P i) p₀ (Y.flow (Array.stamp (Ship.yardSky F b hN p) (F.beta N p) u) i j) (fun _ => Ship.allowance A m k) q.coast.e s (s*w (A.clock.hatBeta i))

-- Closed price iteration, no assumption that middle spacing remained Δ when reaching width site.
theorem coversSky {T : Config G (F.side N p) → veil (Fin v)} (U : ExhibitsSky Y P b X m hN T q) (hr : AllowedSky F.path.levels b k)
    (hq : Tally (wheelSky F.path.levels k) (F.path.levels.clock.hatBeta k) q m)
    (hL : ∀ u, widthSky F.path.levels b k ≤ u → u≤middleSky F.path.levels b k →
      F.path.levels.clock.hatBeta u∈ Icc (F.path.levels.clock.hatBeta k/2) (F.path.levels.clock.hatBeta k))
    (hh : settledSky Y P b X m hN q T le_rfl) :
    Ship.estimateSky (P (widthSky F.path.levels b k)) Y hN X T q.coast.e 1 1 (Ship.allowance F.path.levels m k) := by
  let A := F.path.levels
  let h := widthSky A b k
  let ℓ := middleSky A b k
  let L := wheelSky A k
  let s := A.clock.hatBeta k
  have hlen : ℓ-h≤more L s := hr.shift
  have hv (j : ℕ) (hm : h ≤ j) : spouse s q (ℓ-j) ≤ Perch.bill (-1/2) s :=
    (partner q (Nat.sub_le_sub_left hm ℓ |>.trans hlen)).trans hq.growth
  have hs (i : ℕ) (p₀ : i≤ℓ) (H : h ≤ i) : settledSky Y P b X m hN q T p₀ := by
    induction p₀ using Nat.decreasingInduction with
    | self => exact hh
    | of_succ j hj IH =>
      have he := U j H hj (IH (H.trans (Nat.le_succ j)))
      unfold settledSky; dsimp only
      rw [Y.flow_step _ j (hj.trans_le ((beforeSky A b k).trans hN))]
      let a₀ := spouse s q (ℓ-(j+1))
      apply follows he
      · have hp : ℓ-j=ℓ-(j+1)+1 := by omega
        have ha : 0<a₀ := spouse_pos ..
        change q.α*a₀+Perch.bill (1/2) s*a₀^2 ≤ spouse s q (ℓ-j)
        have hb : Perch.bill (1/2) s*a₀ ≤ 1 := (mul_le_mul_of_nonneg_left (hv (j+1) (H.trans (Nat.le_succ j))) (show 0 ≤ Perch.bill (1/2) s from (Real.exp_pos _).le)).trans (by unfold Perch.bill; rw [← Real.exp_add]; apply Real.exp_le_one_iff.mpr; linarith only)
        have hc : spouse s q (ℓ-j)=(q.α+1)*a₀ := by unfold a₀ spouse eager; rw [hp,pow_succ]; ring
        rw [hc]; linarith only [mul_le_mul_of_nonneg_left hb ha.le]
      apply (hq.force _ (hL _ (H.trans (Nat.le_succ j)) hj) _ (hL _ H (Nat.le_trans (Nat.le_succ j) hj))).trans
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      calc
        _ = spouse s q 0 := by rw [spouse,pow_zero,one_mul]
        _ ≤ _ := partner q (Nat.zero_le _)
  have hz : settledSky Y P b X m hN q T (widerSky A b k) := hs h (widerSky A b k) le_rfl
  have hp : spouse s q (ℓ-h) ≤ 1 := (hv h le_rfl).trans (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (boil_pos _) (by norm_num)))
  exact follows hz hp ((mul_le_mul_of_nonneg_left (strong _) (spouse_pos s q (ℓ-h)).le).trans (by rwa [mul_one]))
end
end YM.Next.Rank.Perch
