import YM.Next.RANK.Bird
import YM.Next.RANK.Memorandum

/-!
# Pricing the remaining steps

This file: once unmarked control and one-step raw estimate
cases available, go from middle Notice to last.

It's only a **specialized** version
of the estimate (require only at these radii, this iteration, may lose e powers in
starting Shelf and allow g^c ≤ 1 on partner coefficients).

No fake proof from scope
conditions.

Show cumulative threshold compatibility and use explicit receipts for
step growth and support flags.

No ability to retune mark names/discard positions
along way.

This makes no assertion supplied `Rep.beta` was obtained by any
perturbative flow computation, but requires true pushed densities and matching
couplings.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Perch
open Lattice Wilson RG Value Dock Station Peak Cells Read Marker Glyph Filter Set Extraction
open scoped Topology BigOperators Classical

variable {G : Gauge} {n : Side} {P : Rep G n} {A : Type*} [DecidableEq A] [Fintype A]
variable (C : Demand)

-- step tests specialized to THIS one path and collection of markers, uniform post-L constants.
structure Era where
  coast : Demand
  α : ℝ -- multiplier here for (linear+partner ≤1 relative), even post-L allowed on THESE steps
  pay : 1 ≤ α

def eager (i : Era) := i.α+1
lemma eager_one (i : Era) : 1 < eager i := by have h := i.pay; unfold eager; linarith

-- K steps pay all height positions. actual β on history below k may differ from restarted.

def spouse (s : ℝ) (P : Era) (count : ℕ) := eager P ^ count * Perch.bill (-3/4) s
lemma partner {u v} {s : ℝ} (P : Era) (h : u≤v) : spouse s P u ≤ spouse s P v :=
  mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (eager_one _).le h) (Real.exp_pos _).le
lemma spouse_pos (s : ℝ) (P : Era) (count : ℕ) : 0 < spouse s P count :=
  mul_pos (pow_pos (zero_lt_one.trans (eager_one _)) _) (Real.exp_pos _)

/-- Cost tests involve previous width and period, but can ask once at comparison
level k for all of them. -/
structure Tally (L s : ℝ) (P : Era) (m : ℕ) : Prop where
  growth : spouse s P (more L s) ≤ Perch.bill (-1/2) s
  stops u (hu : u∈ Icc (s/2) s) : Shelf P.coast m s u
  force u (hu : u∈ Icc (s/2) s) t (ht : t∈ Icc (s/2) s) : Perch.gas P.coast u ≤ Perch.bill (-3/4) s * w t

private theorem short_step (L : ℝ) (h : 1 < L) (P : Era) {a : ℝ} (ha : 0<a) :
    ∀ᶠ s : ℝ in atTop, (more L s:ℝ) * Real.log (eager P) ≤ a*boil s := by
  let u := Real.log L
  let v := Real.log (eager P)
  have hx : 0<v := Real.log_pos (eager_one _)
  have ht : 0 < u := Real.log_pos h
  filter_upwards [many.eventually_ge_atTop 1, Perch.rate_wall (show (0:ℝ)<u*a/2 from by positivity) (10*v),
    boil_rate.eventually_ge_atTop (2*v/a)] with s hs he hf
  have hp : 1 ≤ (M s:ℝ) := by exact_mod_cast hs
  let z := ((M s:ℝ))^10
  have hz : 1 ≤ z := one_le_pow₀ hp
  have h1 : (more L s:ℝ) < Real.log z / u + 1 := Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg hz) ht.le)
  have h2 : (more L s:ℝ)*u < Real.log z + u := by
    apply lt_of_lt_of_eq (mul_lt_mul_of_pos_right h1 ht); field_simp
  have hw : Real.log (M s:ℝ) ≤ Real.log (walls s:ℝ) := Real.log_le_log (zero_lt_one.trans_le hp) (by unfold walls; push_cast; nlinarith)
  unfold z at h2; rw [Real.log_pow] at h2; push_cast at h2
  have hy := (div_le_iff₀ ha).mp hf
  apply le_of_mul_le_mul_left _ ht
  change u*((more L s:ℝ)*v) ≤ u*_
  linarith only [mul_le_mul_of_nonneg_left h2.le hx.le,he,mul_le_mul_of_nonneg_left hw hx.le,mul_le_mul_of_nonneg_left hy ht.le]

lemma on_time (L : ℝ) (h : 1<L) (P : Era) (m : ℕ) : ∀ᶠ s in atTop, Tally L s P m := by
  filter_upwards [short_step L h P (by norm_num : 0<(1/4:ℝ)),mint P.coast m,
    Perch.force P.coast.posA (3/4) (7/10) (by norm_num) (by norm_num), Perch.half.eventually_ge_atTop (Real.exp 1)] with s hs hh hz hV
  refine ⟨?_,hh,fun u hu t ht => ?_⟩
  · have hp : eager P= Real.exp (Real.log (eager P)) := (Real.exp_log (zero_lt_one.trans (eager_one _))).symm
    unfold spouse; conv_lhs => arg 1; arg 1; rw [hp]
    rw [← Real.exp_nat_mul,Perch.bill,← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith only [hs]
  rw [Perch.bill,w,← Real.exp_add]; apply Real.exp_le_exp.mpr
  linarith only [hz u hu, Perch.join_mono (le_trans hV ht.1) ht.2]

variable {F : Family G} {m k N p v : ℕ} {b : ℝ}

structure Candle (Y : Course F N p k) (u : ℕ) (D : Rep G (F.side u p)) (hi : u ≤ N) : Prop where
  settle : Ship.Settled D Y hi
  budget : D.p.B=Perch.walls (F.path.levels.clock.hatBeta u)
  threshold : D.p.threshold= F.path.levels.clock.hatCoupling u * Perch.hot (F.path.levels.clock.hatBeta u)

/-- Awaiting restarted trajectory. Use widths..middle; not an arbitrary
Canon/R covariance Picard choice. Exact stamps & vacuum density with actual same
kernels and only changing allowable numerical couplings along the course. -/
def Path (Y : Course F N p k) (P : (u : ℕ) → Rep G (F.side u p)) (hi : k ≤ N) (b : ℝ) :=
    let A := F.path.levels
    ∀ u, width A b k ≤ u → ∀ h : u ≤ middle A b k, Candle Y u (P u) (h.trans ((before A b k).trans hi))

-- step bound at fixed v specialized to one arc.
section
variable {q : Era} (Y : Course F N p k) (P : (u : ℕ) → Rep G (F.side u p))
variable (b : ℝ) (X : Points v) (m : ℕ) (hN : k ≤ N)

def Exhibits (U : Config G (F.side N p) → veil (Fin v)) (q : Era) : Prop :=
    let A := F.path.levels
    let ℓ := middle A b k
    let s := A.clock.hatBeta k
    let S := Array.stamp (Ship.yard F b hN p) (F.beta N p) U
    let d := fun _ : (Ship.yard F b hN p).Cell × Fin v => Ship.allowance A m k
    ∀ j, width A b k ≤ j → ∀ H : j<ℓ,
      let i : j+1 ≤ N := (show j+1 ≤ ℓ from H).trans ((before A b k).trans hN)
      let u := A.clock.hatBeta (j+1)
      let C := Y.flow S (j+1) i
      let p₀ := readers (C:=F) (b:=b) (p:=p) X hN i
      let p₁ := readers (C:=F) (b:=b) (p:=p) X hN ((Nat.le_succ j).trans i)
      let z := spouse s q (ℓ-(j+1))
      Notice (P (j+1)) p₀ C d q.coast.e z (z*w u) →
        Notice (P j) p₁ ((A.clock.op j p).push (Y.changeβ (j+1)) C) d q.coast.e (q.α*z+Perch.bill (1/2) s*z^2) (Perch.gas q.coast u)

lemma follows {A : Type*} [DecidableEq A] [Fintype A]
    {D : Rep G n} {ζ : A → Site n} {E : Config G n → veil A} {r : A → ℝ} {h1 h2 v1 v2 b : ℝ}
    (H : Notice D ζ E r b h1 v1) (he : h1≤h2) (hv : v1 ≤ v2) : Notice D ζ E r b h2 v2 := by
  obtain ⟨α,β,ha,hb,f,g,h,hbg,⟨a,he₁,he₂⟩, b,hv₁,hv₂⟩ := H
  exact ⟨α,β,ha,hb,f,g,h,hbg,⟨⟨a,he₁,fun i => (he₂ i).trans he⟩, b,hv₁,fun x => (hv₂ x).trans hv⟩⟩

def settled (q : Era) (u : Config G (F.side N p) → veil (Fin v)) {i : ℕ} (hi : i ≤ middle F.path.levels b k) : Prop :=
    let A := F.path.levels
    let j : i ≤ N := hi.trans ((before A b k).trans hN)
    let p₀ := readers (C:=F) (b:=b) (p:=p) X hN j
    let s := spouse (A.clock.hatBeta k) q (middle A b k - i)
    Value.Notice (P i) p₀ (Y.flow (Array.stamp (Ship.yard F b hN p) (F.beta N p) u) i j) (fun _ => Ship.allowance A m k) q.coast.e s (s*w (A.clock.hatBeta i))

-- Closed price iteration, no assumption that middle spacing remained Δ when reaching width site.
theorem covers {T : Config G (F.side N p) → veil (Fin v)} (U : Exhibits Y P b X m hN T q) (hr : Allowed F.path.levels b k)
    (hq : Tally (wheel F.path.levels k) (F.path.levels.clock.hatBeta k) q m)
    (hL : ∀ u, width F.path.levels b k ≤ u → u≤middle F.path.levels b k →
      F.path.levels.clock.hatBeta u∈ Icc (F.path.levels.clock.hatBeta k/2) (F.path.levels.clock.hatBeta k))
    (hh : settled Y P b X m hN q T le_rfl) :
    Ship.estimate (P (width F.path.levels b k)) Y hN X T q.coast.e 1 1 (Ship.allowance F.path.levels m k) := by
  let A := F.path.levels
  let h := width A b k
  let ℓ := middle A b k
  let L := wheel A k
  let s := A.clock.hatBeta k
  have hlen : ℓ-h=more L s := hr.shift
  have hv (j : ℕ) (hm : h ≤ j) : spouse s q (ℓ-j) ≤ Perch.bill (-1/2) s :=
    (partner q (Nat.sub_le_sub_left hm ℓ |>.trans_eq hlen)).trans hq.growth
  have hs (i : ℕ) (p₀ : i≤ℓ) (H : h ≤ i) : settled Y P b X m hN q T p₀ := by
    induction p₀ using Nat.decreasingInduction with
    | self => exact hh
    | of_succ j hj IH =>
      have he := U j H hj (IH (H.trans (Nat.le_succ j)))
      unfold settled; dsimp only
      rw [Y.flow_step _ j (hj.trans_le ((before A b k).trans hN))]
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
  have hz : settled Y P b X m hN q T (wider A b k) := hs h (wider A b k) le_rfl
  have hp : spouse s q (ℓ-h) ≤ 1 := (hv h le_rfl).trans (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (boil_pos _) (by norm_num)))
  exact follows hz hp ((mul_le_mul_of_nonneg_left (strong _) (spouse_pos s q (ℓ-h)).le).trans (by rwa [mul_one]))
end
end YM.Next.Rank.Perch
