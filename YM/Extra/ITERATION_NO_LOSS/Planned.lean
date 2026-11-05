import YM.Extra.ITERATION_NO_LOSS.Mechanism

/-!
# Conditional RLoops multi-stage conclusion
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration
open Filter Function Lattice Wilson RG RG.Supply Precision Pressure Tree Bloch Bid Craft Input Calibration Inherited
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {S : Sheet G} {D : Rolls S} {Θ : Protection D} {W : Supply.Delays Θ} {Y : Bar W} {I : Wait Y}
variable {a : Levels G} {M : Horizon a} {K : MapPrices} {U : Apertures} {A : ClassicalCosts} {H : QuantumCosts}
    {Q : PostCost D} {O : ChartRatio G} (hc : Before S U A H K) (hw : Warm H W) (hp : Paid I a) (hm : M.Suffices K)
    (hg : GapQuote D K Q) (hO : LocalRatio O) (hB : ∀ N m : ℕ, m ≤ N → ∀ p, Sworn (M.H N m) (a.S.side m p) G)
    (hT : ∀ N m : ℕ, m < N → Harmonic (M.towers N m)) (hR : Rates M K U A H Q O)

include hc hw hp hm hg hO hB hT hR
theorem sweep {n i : ℕ} (h : i ≤ n) : ∃ (T : ℕ → PathData G) (b : ℕ → ℝ) (ρ : ∀ m, Branch a m),
    Peak M K U A n (T n) ∧ ∀ m : ℕ, i ≤ m → m < n → Move M K U A Q O n m (T (m+1)) (T m) (ρ m) (b m) := by
  classical
  induction h using Nat.decreasingInduction with
  | self =>
    obtain ⟨R,hR⟩ := peak hc hp hm hB hR n
    exact ⟨fun _ => R, fun _ => 0,fun _ _ _ => 0,hR,fun m hm he => False.elim (hm.not_gt he)⟩
  | of_succ i hi IH =>
    obtain ⟨T,b,ρ,ht,hh⟩ := IH
    obtain ⟨R,t,α,H⟩ := extend hc hw hp hm hg hO hB hT hR hi (T:=T (i+1)) (by
      rcases (show i+1 ≤ n from hi).eq_or_lt with h|h
      · rw [h]; exact ht.ticket
      · exact (hh _ le_rfl h).ticket)
    refine ⟨Function.update T i R, Function.update b i α, Function.update ρ i t, ?_,fun m hm he => ?_⟩
    · rwa [update_of_ne hi.ne']
    rcases hm.eq_or_lt with hv|hv
    · subst m; simpa only [update_self,update_of_ne (Nat.lt_succ_self i).ne']
    simp only [update_of_ne hv.ne', update_of_ne (hv.trans (Nat.lt_succ_self m)).ne']; exact hh m hv he

theorem planned : ∃ F : Kin M O, F.Planned Q ∧ ∀ N m, m ≤ N → Ticket M K U A N m (F.path N m) := by
  choose T b ρ hb ht using fun n => sweep hc hw hp hm hg hO hB hT hR (Nat.zero_le n)
  have hx (n m : ℕ) (hm : m ≤ n) : Ticket M K U A n m (T n m) := by
    rcases hm.eq_or_lt with h|h
    · subst m; exact (hb n).ticket
    exact (ht n _ (Nat.zero_le _) h).ticket
  have hl (n m) (hm : m<n) := ht n m (Nat.zero_le _) hm
  exact ⟨⟨b,T,ρ⟩,
    { stage := hp.stage.symm
      lengths := hp.lengths.symm
      links := fun N m h => (hx N m h).rooted.attached
      cap := fun N m h => (hx N m h).funded
      peak := fun N => (hb N).peak
      initial := fun N => (hb N).initial
      gap := fun n m p hm => (hl n m hm).shell.gap p
      critical := fun n m p hm F => ⟨(hl n m hm).shell.critical p F,(hl n m hm).shell.guessed p F⟩
      classicalPart := fun n m p hm => (hl n m hm).classicalPart p
      kinetic := fun n m hm => (hl n m hm).kinetic
      retains := fun n m p hm => (hl n m hm).thermal p }, hx⟩
end YM.Extra.Iteration
