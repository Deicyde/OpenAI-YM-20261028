import YM.MergeProof.Buys
import YM.MergeProof.Cashew
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories Ac Bid
open Planned.GuardedAtom Accent PhysicalNext.Repeat.Lotus Motion
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{d:ℕ} (H:History G) (A:Hol G){F:Labels.Frame G d}(T:SectionData F)
   (W:Bid.Worth)(ζ u ψ:ℕ→ℝ)(t:ℝ)(k N p:ℕ) (M:Extra.Histories.Music F H N p)
set_option quotPrecheck false
local notation "K"=> H.levels
local notation "P"=> H.levels.budget
local notation "Γ"=> (fun m=>(H.levels.params m).columns)
local notation "R"=> H.rep N p
local notation "Gx"=> M.tone
local notation "X"=> alto H
set_option quotPrecheck false
-- independent demand.Degraded.
structure Fiesta (F:Labels.Frame G d) (ζ ψ:ℕ→ℝ) (k:ℕ) :Prop where
    coin m : k ≤ m → ζ m* Γ m ≤ 1
    room m : k ≤ m → 2*orbitCost F*(ψ m+2*Γ (m+1))*ζ (m+1) ≤ 1
    tap m : k ≤ m → 0 ≤ ψ m
structure Banks (F:Labels.Frame G d)(t : ℝ)(u ζ:ℕ→ℝ)(N:ℕ):Prop where
    cost:1 ≤ t
    candle : Real.exp ((P N).supportExponent+2)*fullCost F (P N) t *ζ N ≤ u N
def bond (m:ℕ)(v:F.Coeff):= ‖alto H m d‖* F.coeffSize ((M.tone m).index v)
local notation "Λ"=> bond H N p M
variable (i m:ℕ)(v:F.Coeff)(r b:ℝ)
lemma cost_step (hI:r*Λ i v≤ζ i) (hr:0≤r)(hb:0≤b)(he:Fiesta H F ζ ψ k) (hp:b≤r)(hx:k ≤ i)
    (hs: b*Λ (i+1) v≤ζ (i+1))(hh:Heard T H N p A i (Gx i)) : b*(‖X i d‖*(Gx i).charge v) ≤ 1 ∧
       2*b*(‖X (i+1) d‖*(orbitCost F*F.coeffSize ((Gx (i+1)).index v) *(ψ i+2*Γ (i+1)))) ≤ 1:=by
    have hw : F.coeffSize (F.core ((Gx i).index v)) ≤ F.coeffSize ((Gx i).index v):= by
       unfold Labels.Frame.coeffSize; apply sum_le_sum; intro j hi; change ‖Function.update ((Gx i).index v) 0 0 j‖ ≤ _; by_cases h:j=0 <;> simp [h]
    have hg (m:ℕ): 0 ≤ Γ m:= zero_le_one.trans ((H.levels.params m).columns_ge)
    have hφ:0 ≤ Λ i v:= mul_nonneg (norm_nonneg _) (Work.G08.size_nonneg ..)
    have hh' :(Gx i).charge v ≤ Γ i * F.coeffSize ((Gx i).index v):= (hh.cone v).trans (mul_le_mul_of_nonneg_left hw (hg i))
    constructor
    · refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh' (norm_nonneg _)) hb).trans ?_
      have hf:b*(‖X i d‖*(Γ i * F.coeffSize ((Gx i).index v)))=b*bond H N p M i v*Γ i:=by unfold bond; ring
      rw [hf]; exact (mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right hp hφ).trans hI) (hg i)).trans (he.coin i hx)
    let f:=2*orbitCost F*(ψ i+2*Γ (i+1))
    have hF:0 ≤ f:=by apply mul_nonneg (mul_nonneg zero_le_two (zero_le_one.trans (orbitCost_one_le F))) (add_nonneg (he.tap i hx) (mul_nonneg zero_le_two (hg _)))
    refine le_trans (le_of_eq (b:=f*(b*Λ (i+1) v)) ?_) ((mul_le_mul_of_nonneg_left hs hF).trans (he.room i hx)); unfold bond f; ring
lemma bout (h:roomCost H.levels W)(hw:Bank W H.levels) (hi:k ≤ i)(hx:i<N)(hs:Sung T H N p A W k M): Λ (i+1) v ≤ ((H.S.block i).val:ℝ)^d*Γ (i+1)*Λ i v := by
    have he := hs.step i hi hx; have hz:= hs.earned i hi hx.le; let L:=H.S.block i
    have hy:= hs.earned (i+1) (hi.trans i.le_succ) hx; have hc:=hy.cone v; have hd:= he.tally v; rw [hz.currents v,hy.currents v] at hd
    have hp : F.coeffSize _ ≤ _:= (Work.G08.cone_step W H h hw i F _ _ _ _ hd hc).2.1; unfold bond; rw [alto_at,norm_mul,norm_pow]
    apply le_trans (mul_le_mul_of_nonneg_left hp (_ : 0 ≤ ‖(L.val:ℂ)‖^d * ‖X i d‖)) (le_of_eq ?_)
    · positivity
    rw [Complex.norm_natCast]; unfold L; ring
variable (w:ℕ→ℝ)
lemma cost_chain {κ:ℕ}(hp:κ≤k) (hb:∀ i,k ≤ i→ i≤N→ 0≤ w i)(hV:k≤N)(he : ∀ i,k ≤ i → i<N→
    w (i+1) * (((H.S.block i).val:ℝ)^d*Γ (i+1)) * ζ i ≤ ζ (i+1)*w i)(hc:∀ i,k ≤ i→i<N → 0<w i)(h:roomCost H.levels W)(hx:Bank W H.levels)(hh:Sung T H N p A W κ M)(hμ:w k*Λ k v ≤ ζ k) : ∀ i,k ≤ i→ i≤N→ w i* Λ i v ≤ ζ i := by
    intro i hi hy
    induction hi with
    | refl=> exact hμ
    | step ih IH=> rename_i i; have hR:= IH (show i≤N by omega); have hW : 0 < w i:= hc i ih hy
                   apply le_trans (mul_le_mul_of_nonneg_left (bout _ _ _ _ _ _ _ _ i v h hx (hp.trans ih) hy hh) (hb _ (Nat.le_trans ih i.le_succ) hy)); apply le_of_mul_le_mul_right (a:=w i) _ hW
                   let t :ℝ:= w (i+1)*(((H.S.block i).val:ℝ)^d*Γ (i+1)); have ht : 0 ≤ t:= mul_nonneg (hb _ (Nat.le_trans ih i.le_succ) hy) (mul_nonneg (by positivity) (zero_le_one.trans (H.levels.params _).columns_ge))
                   exact le_trans (le_of_eq (b:=t*(w i*Λ i v)) (by unfold t; ring)) ((mul_le_mul_of_nonneg_left hR ht).trans (he i ih hy))
end YM.MergeProof
