import YM.Next.RANK.Incoming
import YM.Next.RANK.Voucher

/-!
# This charge can be scheduled (in isolation)

Freeze a pre/post catalogue *before* choosing the clock. This only checks
Tally and determinant can in fact be paid in the numerical receipts in RPost
when entrance of W and restart and upper rank equations etc available. More tests
must be simultaneous, poses **no** Factory existence claim. Don't apply this
to a lagging B-j clock then raise the receipts after without redoing upstream.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Peak
open Lattice Perch Filter Asymptotics Real RG RG.Supply Set Ship Station
open scoped Topology BigOperators Classical

variable {G : Gauge} {p : Sheet G} {w : Rolls p} {T : Protection w} {D : Delays T} (Z : Bar D)

-- Cost of h stretch in sigma confined to s/2. Here j param fixed under InWindow, not chosen by this gate.

def cardTest (O : HaarBudget G) (k m : ℕ) (b : ℝ) (d : Era) (s : ℝ) :=
    Tally ((w.L k).val:ℝ) (preHat Z s) d m ∧ (benchCost Z b k s:ℝ)*Real.log (w.L k).val*G.slopeConstant ≤ preHat Z s/2 ∧
      Station.ticket O (p.profile k) m ≤ amount Z m s

theorem reserves (h : G.Simple) (k m : ℕ) (hm : 0<m) (b : ℝ) (hb : 0≤b) (d : Era) (O : HaarBudget G) :
    ∀ᶠ s in atTop, cardTest Z O k m b d s := by
  let u := Real.log (w.L k).val
  have hc := Gauge.slopeConstant_pos h
  have hf := ((accommodate Z b k h hb).mul_const u).mul_const G.slopeConstant; rw [zero_mul,zero_mul] at hf
  have he : Tendsto (preHat Z) atTop atTop := Filter.tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop hc)
  have hv : 1 < ((w.L k).val:ℝ) := by exact_mod_cast (by have ht := (w.large k).size; omega : 1 < (w.L k).val)
  filter_upwards [(able Z h m hm).eventually_ge_atTop _,hf.eventually (ge_mem_nhds (show 0 < G.slopeConstant/2 by linarith)),
    he.eventually (on_time (↑(w.L k).val:ℝ) hv d m),eventually_gt_atTop 0] with s hs hf he hp
  refine ⟨he, ?_, hs⟩
  rw [div_mul_eq_mul_div,div_mul_eq_mul_div,div_le_iff₀ hp] at hf; unfold preHat
  change _ * u * _ ≤ _; linarith only [hf,Z.good]

def Fired (B : Wait Z) (O : HaarBudget G) (j : ℕ) (b : ℝ) (m : ℕ) (d : Era) := ∀ s : ℝ,B.readyHere j ≤ s →
    cardTest Z O j m b d s ∧ benchCost Z b j s ≤ B.window j s

-- Simpler using honoured for bench part
lemma served (h : G.Simple) (O : HaarBudget G) (B : Wait Z) (M : ℕ → ℕ) (b : ℕ → ℝ) (E : ℕ → ℕ → Era) (J : ℕ → Finset ℕ)
    (hm : ∀ i, 0 < M i) (hb : ∀ i,0 ≤ b i) :
    ∃ W : Wait Z, B.minLength ≤ W.minLength ∧ (∀ j,B.readyHere j ≤ W.readyHere j ∧ (∀ s,B.window j s ≤ W.window j s)) ∧
      ∀ j i,i∈J j → Fired Z W O j (b i) (M i) (E j i) := by
  obtain ⟨P,hL,hs,hP⟩ := honoured Z (P:=B) h O M b hb J hm
  have he (j : ℕ) : ∀ᶠ s in atTop,∀ i∈ J j, cardTest Z O j (M i) (b i) (E j i) s :=
    (eventually_all_finset _).2 (fun i _ => reserves Z h j _ (hm i) _ (hb i) (E j i) O)
  choose v hv using fun j => eventually_atTop.mp (he j)
  let W : Wait Z := { P with readyHere := fun j => max (P.readyHere j) (v j) }
  refine ⟨W,hL,fun j => ⟨(hs j).1.trans (le_max_left ..), (hs j).2⟩,fun j i hi s h => ?_⟩
  exact ⟨hv j s ((le_max_right ..).trans h) i hi,(hP j i hi s ((le_max_left ..).trans h)).2⟩

variable {Z}
lemma held_at (B : Wait Z) (a : Levels G) (h : Paid B a) {j k : ℕ} (hb : p.first<j)
    (hk : a.clock.J k=j) (hs : B.readyHere j ≤ a.S.scale k) (hf : B.window j (a.S.scale k)≤k)
    (hm : ∀ i,k-B.window j (a.S.scale k) ≤ i → i≤k → a.clock.J i=j)
    (O : HaarBudget G) (m : ℕ) (b : ℝ) (D : Era) (hi : Fired Z B O j b m D) (hg : G.Simple) : Charge a b k m O D := by
  let s := a.S.scale k
  let u := wheel a k
  have he : preHat Z s=a.clock.hatBeta k := by rw [preHat, Calendar.hatBeta,h.bar]
  have hp : u=((w.L j).val:ℝ) := by dsimp only [u]; rw [wheel,h.lengths,hk]
  obtain ⟨⟨H,I,T⟩,Q⟩ := hi s hs
  unfold benchCost at Q; rw [he,← hp] at Q; change height a b k + surplus a k ≤ _ at Q
  unfold benchCost at I; rw [he,← hp] at I; push_cast at I
  have hA : Allocated a m k O b := by
    have ht : a.params k=p.profile j := by change a.clock.stage _=p.profile j; rw [h.stage,hk]
    refine ⟨⟨?_,Q.trans hf,fun i ha hb => ?_⟩,?_⟩
    · by_contra! hj; rw [Nat.le_zero.mp hj,h.firstZero] at hk; omega
    · apply (hm i ?_ hb).trans hk.symm
      unfold width middle at ha; change k-B.window j s ≤ _; omega
    rw [ht]; unfold amount at T; rw [he] at T; exact T
  rw [he,← hp] at H
  refine ⟨hA,H,fun i hk hi => ?_⟩
  have hv := (Stock.a_log a.S i); have he' := hA.permitted.scales i k hk (hi.trans (before ..)) le_rfl
  have hi' : a.S.scale k-a.S.scale i=(k-i:ℕ)*Real.log u := by
    have hb := congr_arg Real.log he'
    rw [Real.log_div (a.S.a_pos _).ne' (a.S.a_pos _).ne',Real.log_pow] at hb
    rw [hv,Stock.a_log] at hb; simp only [Real.log_exp] at hb; linarith only [hb]
  have H' : 0 ≤ Real.log u := (Real.log_pos hA.permitted.large).le
  have hz : k-i ≤ height a b k + surplus a k := by unfold width middle at hk; omega
  have ha := Gauge.slopeConstant_pos hg; refine ⟨?_,?_⟩
  · have hy : (k-i:ℕ)*Real.log u*G.slopeConstant ≤ a.clock.hatBeta k/2 := by
      refine le_trans ?_ I; gcongr; exact_mod_cast hz
    dsimp only [Calendar.hatBeta] at hy ⊢; rw [← hi'] at hy; linarith only [hy]
  have ht : 0 ≤ a.S.scale k-a.S.scale i := hi' ▸ mul_nonneg (Nat.cast_nonneg _) H'
  exact add_le_add_right (mul_le_mul_of_nonneg_left (sub_nonneg.mp ht) ha.le) _

-- Allocation channel support, no changing Era or Paid at the stage after costs.

end YM.Next.Rank.Peak
