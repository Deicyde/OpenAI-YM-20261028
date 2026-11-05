import YM.FullVolume.Train.Wheels
/-! adapt pinning for glow builds preserving Q records -/
set_option autoImplicit false
noncomputable section
namespace YM.Bid
open Filter Function Lattice RG Wilson Precision Tree Exterior Bloch Laurent Pressure
open Craft Next Next.Free
open Matrix (IsHermitian transpose)
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal InnerProductSpace
variable {G:Gauge}{A: Levels G}(W: ℕ→ ℝ)
structure Committed (B T: Horizon A) (N i:ℕ) (T': C3) (y X z:ℝ): Prop where
  generated p: Replaces (A.clock.op i p).ratio (B.H N (i+1)) (B.H N i) (A.params (i+1)).clip (A.params i).clip (A.clock.op i p).kernel.penalty T' (B.towers N i) (T.towers N i)
  funds : Funds T' y X
  strip : T'.strip z X
  square : SqActs (glow A W N i) T'
theorem pinsT (W:ℕ→ℝ) (b : F07) (c : F08) (d : F09) {G : Gauge} (P : Supply.Sheet G) (Q : MapPrices) :
    ∃ K : MapPrices, ∀ A : Levels G,A.clock.stage=P.profile → A.clock.kernel=P.kernel →
      ∀ B : Horizon A, Exhibits A Q B W → ∃ T : Horizon A, Retained T B ∧ T.Suffices K ∧ ∃ y X z:ℕ→ℝ,(∀ i,0<y i)∧(∀ i,0<z i)∧∀ N i,i<N→ let j:=A.clock.J (i+1); ∃ T',Committed W B T N i T' (y j) (X j) (z j) := by
  classical
  choose y X z hy hz H' using fun i : ℕ => b (TypeFace 3) (Q.Ω i) (Q.η i) (Q.α i) (Q.eta_pos i) (Q.alpha_pos i)
  choose t u ht I using fun i j : ℕ => c (P.profile j).clip (P.profile i).clip P.kernel.penalty (Q.Ω j) (Q.α j) (Q.α i)
    (Q.Ω i) (z j) (X j) (j-2) P.kernel.penalty_pos (Q.alpha_pos j) (Q.alpha_pos i) (hz j)
  let K : MapPrices := { Q with
    α := fun j => min (Q.α j) (min (t j j) (t (j-1) j))
    Ω := fun j => max (Q.Ω j) (max (u j j) (u (j-1) j))
    alpha_pos := fun j => lt_min (Q.alpha_pos j) (lt_min (ht j j) (ht _ _)) }
  refine ⟨K,fun A he hb B RZ => ?_⟩
  have R:= RZ.classic
  have hm (N i : ℕ) : ∃ T : Towers (A.S.block i), i < N →
      let S := B.towers N i; let j := A.clock.J (i+1); let W' := B.H N (i+1); let Y := B.H N i
      T.Deep (K.α j) (K.Ω j) (j-2) ∧ T.A0=S.A0 ∧ T.T=S.T ∧ (∀ p : ℕ,
        Towers.Diagonal (A.clock.op i p) W' Y T ∧ Towers.Roll (A.clock.op i p) W' Y T (A.params (i+1)).clip (A.params i).clip) ∧ ∃ F, Funds F (y j) (X j) ∧ F.strip (z j) (X j) ∧ SqActs (glow A W N i) F ∧ ∀ p, Replaces (A.clock.op i p).ratio W' Y (A.params (i+1)).clip (A.params i).clip (A.clock.op i p).kernel.penalty F S T := by
    by_cases Hn : i<N
    · let j := A.clock.J (i+1)
      let k := A.clock.J i
      have hk : k=j ∨ k=j-1 := by
        have hx : k ≤ j := A.fits.mono (Nat.le_succ i)
        have hh : j ≤ k+1 := A.fits.stepSlow i
        omega
      have hs : (A.params i).clip = (P.profile k).clip := by unfold Levels.params Calendar.params; rw [he]
      have ha : (A.params (i+1)).clip = (P.profile j).clip := by unfold Levels.params Calendar.params; rw [he]
      let M:=glow A W N i
      obtain ⟨hM,hr,g2⟩:= RZ.deposits N i Hn
      obtain ⟨M',hn,hM',hSq⟩ := H' _ M hM hr
      let l := A.S.block i
      obtain ⟨T,hF,hT⟩ := I k j (B.H N (i+1)) (B.H N i) (R.covers _ _ Hn) (R.covers _ _ Hn.le)
        _ hM' l (A.S.block_odd i) _ (R.legs N i Hn)
      have hh (p : ℕ) : Replaces (A.clock.op i p).ratio (B.H N (i+1)) (B.H N i) (A.params (i+1)).clip (A.params i).clip
          (A.clock.op i p).kernel.penalty M' (B.towers N i) T := by rw [hs,ha,show (A.clock.op i p).kernel=P.kernel from hb]; exact hT _ _ _
      refine ⟨T,fun _ => ?_⟩
      refine ⟨?_, (hh 0).first.symm, (hh 0).form.symm, fun p => ⟨?_, d _ _ _ _ _ _ _ M' M _ _ _ _ _ _ (hh p) (R.traces _ _ Hn _) (R.traces _ _ Hn.le _) (R.crosses _ _ _ Hn) (fun n => (hSq n).1) (g2 p)⟩, M',hn,hM',hSq,hh⟩
      · have hα : K.α j ≤ t k j := le_trans (min_le_right ..) (hk.elim (fun he => by rw [he]; exact min_le_left ..) (fun he => by rw [he]; exact min_le_right ..))
        have hΩ : u k j ≤ K.Ω j := le_max_of_le_right (hk.elim (fun he => by rw [he]; exact le_max_left ..) (fun he => by rw [he]; exact le_max_right ..))
        obtain ⟨u1,u2,u3,u4⟩ := hF
        exact ⟨fun i j => (u1 i j).mono hα hΩ, fun i j => (u2 i j).mono hα hΩ,fun i j => (u3 i j).mono hα (div_le_div_of_nonneg_right hΩ (by positivity)),fun a hh => ⟨fun i j => ((u4 a hh).1 i j).mono hα (div_le_div_of_nonneg_right hΩ (by positivity)),fun i j => ((u4 a hh).2 i j).mono hα (div_le_div_of_nonneg_right hΩ (by positivity))⟩⟩
      · obtain ⟨h1,h2,h3⟩ := R.crosses N i p Hn
        constructor
        · rw [show T.A0=_ from (hh p).first.symm]; exact h1
        · rw [show T.T=_ from (hh p).form.symm]; exact h2
        rw [show T.A0=_ from (hh p).first.symm, show T.T=_ from (hh p).form.symm]; exact h3
    exact ⟨B.towers N i,fun H => False.elim (Hn H)⟩
  choose t hT using hm
  let T := { B with towers := t }
  refine ⟨T,⟨rfl,fun N i ha => ⟨(hT _ _ ha).2.1,(hT _ _ ha).2.2.1⟩⟩,?_,y,X,z,hy,hz,?_⟩
  swap
  · intro N i hi j; obtain ⟨F,h,u,e,H⟩:= (hT _ _ hi).2.2.2.2; exact ⟨F,H,h,u,e⟩
  refine ⟨fun N i hi => ?_, fun N i hi n => ?_,fun N i hi => (hT N i hi).1,fun N i p hi => ((hT N i hi).2.2.2.1 p).1,
    fun N i p hi => ((hT N i hi).2.2.2.1 p).2, R.top⟩
  · obtain ⟨h1,h2,h3,h4,h5⟩ := R.covers N i hi
    exact ⟨fun x y => (h1 x y).mono (min_le_left ..) (le_max_left ..),fun x y => (h2 x y).mono (min_le_left ..) (le_max_left ..),fun x y => (h3 x y).mono (min_le_left ..) (le_max_left ..),fun x y => (h4 x y).mono (min_le_left ..) (le_max_left ..),fun x y => (h5 x y).mono (min_le_left ..) (le_max_left ..)⟩
  have hp := R.traces N i hi n
  refine { hp with uniform := ⟨fun x => ?_,fun x => ?_⟩ }
  · have hΩ := hp.uniform.1 x
    exact ⟨hΩ.1,hΩ.2.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (by unfold dotProduct; apply Finset.sum_nonneg; intro i _; rw [← sq]; positivity))⟩
  have hΩ := hp.uniform.2 x
  exact ⟨hΩ.1,hΩ.2.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (by unfold dotProduct; apply Finset.sum_nonneg; intro i _; rw [← sq]; positivity))⟩

end YM.Bid
