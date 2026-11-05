import YM.RG08.Ratio.Ephemeral
import YM.RG08.Gaussian.Report

/-!
# Independent WB prescription finite cutoff, complete unmasked ACTION.
General adjacent smoothing & lengths from actual kernel data. No invocation
of continuity of actual symbols/generators. Does not yet give MASK-aware
 estimates or Gram reports. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Chain
open Filter MeasureTheory
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset Next.Free
open PertExtension.Series.Tested PertExtension.Series.Radial Matrix Reflect Conductor Bloch
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} (X : Chain) (i : G.ColorIndex) (D : ChartRatio G)

def column (G : Gauge) (X : Chain) (N m : ℕ) := quad G (X.K₀ N m)

def stampRaw (F : Air G) (N m : ℕ): Air G := strike i (X.patch m) D X.kernel (X.trees m) (X.history N (m+1)) F

def album (N m : ℕ) : Air G := if m<N then correct i (stampRaw X i D (album N (m+1)) N m) (column G X N m) else wilsonTop i
termination_by N-m

def compassRaw (N m : ℕ) : Air G := X.stampRaw i D (X.album i D N (m+1)) N m
lemma album_top (N : ℕ) : X.album i D N N=wilsonTop i := by rw [album,if_neg]; omega
lemma album_step {m N} (h:m<N) : X.album i D N m = correct i (X.compassRaw i D N m) (column G X N m) := by rw [album, if_pos h]; rfl
lemma high_stocks (N m) : Tunable (column G X N m) ∧ Glows (column G X N m) ∧ probeK i (column G X N m)=1 := by
  let B:= X.metric N m; have hp := X.metric_whole N m
  have he t := X.metric_sym N m t
  obtain ⟨hx,hF,H⟩:=price_stanza G hp he 1
  exact ⟨hx,hF,marked_units i _ hp he (X.metric_start ..)⟩
-- every rollout from levels accepted geometry; only wake
structure Packed (i : G.ColorIndex) (Q : Pot G 2) (F : Air G) : Prop where
  gets : Gets F
  halt : Halt F
  balance : Balanced i F
  opens : ∀ m, Faithful Q F m

lemma raw_class (h : X.Wake G) (hp : LocalRatio D) {m N} (hs : m<N) (F : Air G) (he : Packed i (column G X N (m+1)) F) :
    Gets (stampRaw X i D F N m) ∧ ∀ p : Side, Faithful (column G X N m) (stampRaw X i D F N m) p := by
  refine ⟨strike_known (X.patch m) D X.kernel (X.trees m) i _ he.1 (h m),?_⟩ -- order?
  intro p; exact (legal i (X.patch m) X.kernel (X.trees m) (X.history N (m+1)) D (X.metric N m) hp (h m) he.gets he.halt he.opens (X.metric_whole ..) (X.metric_sym N m) (fun c f ht=> ⟨_, X.canonical N m hs ht⟩) p).2
lemma stamp_value (h : X.Wake G) (hp : LocalRatio D) {m N} (hs : m<N) (F : Air G) (he : Packed i (column G X N (m+1)) F) :
    Packed i (column G X N m) (correct i (stampRaw X i D F N m) (column G X N m)) := by
  obtain ⟨hf,H⟩:= raw_class X i D h hp hs F he; obtain ⟨hx,hY,hQ⟩:= X.high_stocks i N m
  exact ⟨traffic i _ _ hf hx hY,(corrigendum ..).2,trueUP i _ _ hf hY hQ,fun p=> remake i _ _ hf (H _) hx⟩
theorem packing (h : X.Wake G) (hp : LocalRatio D) {m N} (he : m ≤ N) : Packed i (column G X N m) (X.album i D N m) := by
  induction he using Nat.decreasingInduction with
  | self=> rw [album_top]; unfold column K₀; rw [X.metric_wilson]; exact ⟨(top_gets ..).1,(top_gets ..).2,sunCorrect i,dawn_truth i⟩
  | of_succ k hk ih=>rw [album_step X i D hk]; exact stamp_value _ _ _ h hp hk _ ih
lemma rawStep (h : X.Wake G)(hp : LocalRatio D) {m N} (hs:m<N) : Gets (X.compassRaw i D N m) ∧ ∀ p,Faithful (column G X N m) (X.compassRaw i D N m) p :=
  raw_class X i D h hp hs _ (packing X i D h hp hs)
end YM.RG08.Chain
