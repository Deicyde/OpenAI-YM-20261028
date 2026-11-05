import YM.WilsonBulk.Vacuum.Schur
import YM.WilsonBulk.Grid.Limits

/-!
UV rates for the flat primitive `∼exp(-c(s_N-s_m))`. Includes endpoints at the top.
All terms at scales below base ℓ (geometry not meeting the large-parameter requests)
are EXCLUDED here. Same convention for all later moment estimates.

These pricing/length hypotheses fix scope of formal program. We include preliminary proofs that
step demands on L work with all larger sizes after these widths are chosen. With these demands
the contraction estimates are proved, not postulated. Whether existing particular Finals and
producer calendars support those additional arithmetic demands (and strengthened delays) is
separate; don't infer from CLOSED.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Lattice Laurent Filter Function Bloch
open Push.AbsoluteSums RG Work.F08 Precision Exterior
open scoped Topology BigOperators Classical
variable {G : Gauge} {A : Levels G}

-- expansion-eta (losses on comparison) never slipped into formal assumptions
structure FlatRequest (A : Levels G) (F F' : MapPrices) (ℓ : ℕ) (σ : ℕ → ℝ) (a : ℝ) : Prop where
  J m : ℓ≤m → 5 ≤ stage A (m+1)
  pos m : ℓ≤m → 0<σ m
  stageWidth m : ℓ≤m → σ m ≤ min (F.α (stage A m)) (F'.α (stage A m)) ∧
    σ m ≤ min (F.α (stage A (m+1))) (F'.α (stage A (m+1)))
  keep m : ℓ≤m → σ m / L A m ≤ σ (m+1)/2
  large m : ℓ≤m → kineticBill (F.Ω (stage A (m+1))) (F'.Ω (stage A (m+1))) (σ (m+1)) (σ m) / L A m
                      ≤ L A m ^ (-a)

variable {P H : Horizon A} {F F' : MapPrices} {ℓ k N N' m : ℕ} {w c a : ℝ} {σ : ℕ → ℝ}

-- before numerical `L`. Stage version for use with `Supply.Rolls.eventually_large` etc.
-- quantifier order: input/output MapPrices -> widths -> thresholds -> L.
lemma hessian_invoice (X Y u v b : ℝ) (hv : 0<v) (hb : b<1) :
    ∀ᶠ n : ℕ in atTop, u/(n:ℝ) ≤ v/2 ∧ kineticBill X Y v u / n ≤ (n:ℝ)^(-b) := by
  have hy : Tendsto (fun n:ℕ => u / (n:ℝ)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x:=u)).div_atTop tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun n:ℕ => (n:ℝ)^((-b+1):ℝ)) atTop atTop := by
    exact (tendsto_rpow_atTop (by linarith : 0< -b+1)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hy.eventually_le_const (half_pos hv), hu.eventually (eventually_ge_atTop
    (kineticBill X Y v u)), eventually_gt_atTop 0] with n hn hs hz
  refine ⟨hn,(div_le_iff₀ (show 0<(n:ℝ) by positivity)).2 ?_⟩
  simpa only [Real.rpow_add (by positivity : 0<(n:ℝ)), Real.rpow_one] using hs

abbrev kcap (F : MapPrices) (j : ℕ) := kprice (F.α j) (F.Ω j)
lemma kcap_nonnegative (R : Horizon A) (h : R.Suffices F) (m : ℕ) :
    0 ≤ kcap F (stage A m) :=
  budget_nonneg ((canonical_strip h (le_refl m)) (coord 0) (coord 0))

lemma propagate (h : H.Suffices F) (h' : P.Suffices F')
    (Q : FlatRequest A F F' ℓ σ a) (hn : N ≤ N') (hm : m ≤ N) (hm₀ : ℓ ≤ m) :
    (minusRows (flat H N m) (flat P N' m)).strip (σ m)
      ((kcap F (stage A N) + kcap F' (stage A N)) * damp A.S a m N) := by
  let B := kcap F (stage A N) + kcap F' (stage A N)
  have hB : 0 ≤ B := add_nonneg (kcap_nonnegative H h N) (kcap_nonnegative P h' N)
  induction hm using Nat.decreasingInduction with
  | self =>
    rw [damp_self,mul_one]
    exact strip_minus (strip_mono (canonical_strip h le_rfl) ((Q.stageWidth _ hm₀).1.trans (min_le_left ..)) le_rfl)
      (strip_mono (canonical_strip h' hn) ((Q.stageWidth _ hm₀).1.trans (min_le_right ..)) le_rfl)
  | of_succ i hi ih =>
    -- pay cost frozen at actual step not longer interval
    obtain ⟨hs,hv⟩ := Q.stageWidth i hm₀
    let b := kineticBill (F.Ω (stage A (i+1))) (F'.Ω (stage A (i+1))) (σ (i+1)) (σ i)
    refine strip_mono (energy_step (Q.pos (i+1) (by omega)) (Q.pos i hm₀).le h h' hi
       (lt_of_lt_of_le hi hn) (Q.J i hm₀) (hv.trans (min_le_left ..)) (hv.trans (min_le_right ..)) (Q.keep i hm₀) (ih (by omega))) le_rfl ?_
    calc _ = (b / L A i)*(B*damp A.S a (i+1) N) := by unfold B b L; ring
         _ ≤ damp A.S a i (i+1)*(B*damp A.S a (i+1) N) :=
            mul_le_mul_of_nonneg_right (by rw [damp_succ]; exact Q.large i hm₀)
              (mul_nonneg hB (damp_pos ..).le)
         _ = B*damp A.S a i N := by rw [mul_left_comm _ B,damp_split]

lemma trim (c a : ℝ) (d : ℕ) (Q : FlatRequest A F F' ℓ σ a)
    (h : H.Suffices F) (h' : P.Suffices F') (hw : 1 ≤ w) (hc : 0≤ c) {b : ℝ} (hb : b<a)
    (hm : m≤N) (hk : ℓ≤m) (hn : N≤N')
    (ht : kcap F (stage A N) + kcap F' (stage A N) ≤ c * age A.S k w N ^ d) :
    (minusRows (flat H N m) (flat P N' m)).strip (σ m)
      (c * momentWeight (a-b) d * age A.S k w m ^ d * damp A.S b m N) := by
  refine strip_mono (propagate h h' Q hn hm hk) le_rfl ?_
  calc _ ≤ c * age A.S k w N ^ d * damp A.S a m N :=
             mul_le_mul_of_nonneg_right ht (damp_pos ..).le
       _ = c * (age A.S k w N ^ d * damp A.S (a-b) m N)*damp A.S b m N := by
          simp only [mul_assoc, damp_fuse, sub_add_cancel]
       _ ≤ _ := by
          rw [mul_assoc c (momentWeight _ _) _]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (age_damp A.S (a-b) k w d hm (sub_pos.mpr hb) hw) hc) (damp_pos ..).le

-- universal costs on age (if integrating into an unbounded uv/printing version, discharge with
-- strengthened schedule delays and geometry; not a bound with N chosen after depth recognized).
-- export also exact norm used by consumer. Use on any cone of fixed σ choices, not a claim
-- at larger width.
def SheetEnd (A : Levels G) (F : MapPrices) (σ : ℕ → ℝ)
    (a : ℝ) (ℓ k : ℕ) (W c : ℝ) (d : ℕ) :=
  FlatRequest A F F ℓ σ a ∧ ∀ i, ℓ ≤ i → kcap F (stage A i) ≤ c * age A.S k W i ^ d

-- not area-floor assertion on any starting historical depths
lemma release_kinetic (c a b : ℝ) (d : ℕ) (h : H.Suffices F)
    (Q : SheetEnd A F σ a ℓ k w c d) (hb : 0< b) (ha : b<a) (hw : 1≤ w) (hc : 0≤ c)
    (hm : ℓ≤m) :
    ∃ T, UVExtension.Free.Received (fun N=>flat H N m) T (σ m) (kcap F (stage A m)) ∧
        ∀ N, m≤N → (minusRows (flat H N m) T).strip (σ m)
          ((c+c) * momentWeight (a-b) d * age A.S k w m ^ d * (A.S.a N / A.S.a m)^b) := by
  have hep (n):= damp_at A.S b m n
  simp_rw [← hep]
  refine release_received (Q.1.pos _ hm).le ?_ ?_ ?_
  · exact (eventually_ge_atTop m).mono fun i hi=> strip_mono (canonical_strip h hi)
      ((Q.1.stageWidth m hm).1.trans (min_le_left ..)) le_rfl
  · simpa only [mul_zero] using (damp_event A.S b (j:=m) hb).const_mul
      ((c+c)*momentWeight (a-b) d*age A.S k w m^d)
  intro i j hi hj; apply trim (c+c) a _ Q.1 h h hw (by positivity) ha hi hm hj ?_
  rw [add_mul]
  exact add_le_add (Q.2 _ (le_trans hm hi)) (Q.2 _ (le_trans hm hi))
end YM.WilsonBulk
