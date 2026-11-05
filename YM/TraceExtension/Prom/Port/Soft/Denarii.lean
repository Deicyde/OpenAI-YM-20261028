import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Denarii
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Coordinates
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Tuning
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Denarii for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Set Filter RG Lattice Wilson Cells Next.Rank Marker Glyph Exponential MeasureTheory Station
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff ENNReal
variable {G : Gauge} {n : Side}
section size
variable {P : Rep G n} (O : HaarBudget G) {σ δ s Λ w : ℝ} (h : Tissue P σ s Λ δ w)
    {X g z : ℝ}

include h

end size
section stamp
open Next.Rank.Array
variable {V : Type} [Fintype V] [DecidableEq V] {F : Family G} {N p m k : ℕ} {T : Tiling (F.side N p)}
variable {X : Config G (F.side N p) → veil V} (c : Course F N p k) (hm : m≤N)

end stamp
section rebate
open Next.Rank.Ship Next.Rank.Read
variable {C : Family G} {N p k M n: ℕ} {x : Points n} {b : ℝ}
theorem couponSky (O : HaarBudget G) (hc : AllocatedSky C.path.levels M k O b) (hb : bank O C.path.levels (widthSky C.path.levels b k))
    {P : Rep G (C.side (widthSky C.path.levels b k) p)} {u : Course C N p k} {hN : k ≤ N} {q : widthSky C.path.levels b k ≤ N}
    (hp : Ferm P u q) (t : Fin n → C.book.Token)
    (B : Fin n → (standard C).Tag) (hx : FitSky C.path.levels b k x) (hn : n ≤ M)
    {e c d : ℝ} (he : 0 ≤ e) (hE : c≤1) (hC : d ≤ 1) (hv : estimateSky P u hN x (invoiceSky B t hx N p) e c d (allowance C.path.levels M k))
    (s : modes (Fin n)) (sh : s.val.Nonempty) :
    let T := yardSky C b hN p
    T.rootTest (C.beta N p) (fun U => (invoiceSky B t hx N p U).part s) ≤ budget C.path.levels M k := by
  intro T
  let A:= C.path.levels; let r:= widthSky A b k
  obtain ⟨H,σ,g,Λ,δ,w,hD,hd⟩ := hp
  have hea := s_postage (X:=invoiceSky B t hx N p) (T:=T) u q O H hd hD.positive hD.entrance hD.assigned rfl (Real.exp_pos _) he (bill_contSky _ _ hx N p) hv s
  let Z := Fintype.card (Site (A.S.side r p))
  rw [Fintype.card_fin, show Fintype.card T.Cell=Z from rfl] at hea
  have hs : d+n*c ≤ 1+(M:ℝ) := by
    refine add_le_add hC ((mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _ : 0 ≤ (n:ℝ))).trans ?_)
    rw [mul_one]; exact_mod_cast hn
  let I := pot A M k
  have hi : protection O P (A.params r).paths Λ δ (d+n*c) g - 4*G.lieDim*Real.log g/(Z:ℝ) ≤ I := by
    apply (hb p P g Λ δ (d+n*c) M hD hs).trans
    change ticket O (A.params r) M ≤ I; exact hc.charge
  apply hea.trans
  let a := allowance A M k
  have ha : 1 ≤ a := fixed ..
  calc
    _ ≤ Real.exp I / a^s.val.card := div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hi) (pow_nonneg (zero_le_one.trans ha) _)
    _ ≤ Real.exp I / a := by
      gcongr
      calc
        a = a^1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ ha (Finset.card_pos.mpr sh)
    _ = _ := by change Real.exp I / Real.exp (2*I)=Real.exp (-I); rw [← Real.exp_sub]; congr 1; ring
end rebate
end YM.PhysicalNext.InteractingRank.Soft
