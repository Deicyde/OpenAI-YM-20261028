import YM.Push.CORRECTED_COLUMNS.Grows
import YM.Push.CORRECTED_COLUMNS.Links
/-!
# N→k→h marker-separation hypotheses in A geometry

The many copies of the determinant test. Keep arbitrary finite absolute
margins (native M_N^a, arbitrary fixed power a). Higher than needed for
some uses; here it works eventually in k. Upstream N→k uncorrected-source
mixed estimates can use this. At *j* between k and h, no assumption
of non-collapse, prove that multiplicity argument etc. still works. Native
distances on each torus. `Progress` doesn't call any calendar gate except
Fits + Series.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Progress
open Lattice RG Wilson MeasureTheory Cells Extraction Function Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius

section Positions
variable (S : Schedule) {r k N p : ℕ} (h : r≤k) (hp : k ≤ N)
private lemma centre (x : Cover) (a : Axis) (he : Positions.Comfortable S r k x) :
    (4:ℤ)*(x a).natAbs ≤ (S.toDepth h p).count.val := by
  specialize he a; have hp := S.embeds_scale (S.toDepth h p)
  have hx : |S.a k*(x a:ℝ)| ≤ S.a r/4 := he
  rw [abs_mul,abs_of_pos (S.a_pos k)] at hx
  have hv : (4:ℝ)*|(x a:ℝ)| ≤ (S.toDepth h p).count.val := by apply le_of_mul_le_mul_left _ (S.a_pos k); linarith
  rw [Int.natCast_natAbs]; exact_mod_cast hv
include h
private lemma clears (x z : Cover) (hx : Positions.Comfortable S r k x) (hz : Positions.Comfortable S r k z) :
    lift (wrap (S.side k p) x-wrap _ z)=x-z := by
  apply lift_eq_iff.2; refine ⟨(_root_.map_sub ..).symm,fun i => ?_⟩
  let T := center S p h 0; have hp : (S.toDepth h p).count.val < (S.side k p).val := T.narrow
  have hxs := centre S h (p:=p) x i hx
  have hzs := centre S h (p:=p) z i hz
  rw [Pi.sub_apply]
  omega
-- compatible lift at *all* m


private lemma gap (x z : Cover) (hx : Positions.Comfortable S r k x) (hz : Positions.Comfortable S r k z) (a b : Site (S.side r p)) (hD : a ≠ b) :
    let T := center S p h (0 : Site (S.side k p))
    let y := T.copyMap a (wrap _ x)
    let v := T.copyMap b (wrap _ z)
    (S.toDepth h p).count.val ≤ 2*separation y v := by
  intro T y v; let H := S.toDepth h p
  have ht : 1 ≤ separation a b := Nat.pos_of_ne_zero fun h => hD ((Corona.line_home a b).symm.trans (Corona.line_end a b h.le))
  have he : H.count.val ≤ separation (H.embed a) (H.embed b) := (le_mul_of_one_le_right (by positivity) ht).trans (Corona.below H _ _)
  have hm (i : T.Cell) (x : Cover) (hx : Positions.Comfortable S r k x) :
      let t := H.embed i
      separation t (T.copyMap i (wrap _ x)) ≤ H.count.val/4 := by
    intro t
    rw [show t=T.copyMap i 0 by simp [t,T,copy_home,H]]
    simp only [Tiling.copyMap,affine, separation_translate,separation_signed]
    unfold separation pdist
    apply Finset.sup_le; intro i _
    have hj := centre S h (p:=p) x i hx
    have hh : Positions.Comfortable S r k 0 := by intro a; change |S.a k*↑(0:ℤ)|≤_; simp only [Int.cast_zero,mul_zero,abs_zero]; exact div_nonneg (S.a_pos _).le (by norm_num)
    have hr : (0:Site (S.side k p)) = wrap _ 0 := (map_zero _).symm
    rw [hr,clears S h 0 x hh hx, Pi.sub_apply,Pi.zero_apply,zero_sub,Int.natAbs_neg]
    unfold H; omega
  have hj : separation (H.embed a) y ≤ H.count.val/4 := hm a _ hx
  have hσ : separation v (H.embed b) ≤ H.count.val/4 := (separation_comm ..).trans_le (hm b _ hz)
  have hτ := separation_triangle y v (H.embed b)
  have hB := separation_triangle (H.embed a) y (H.embed b)
  change H.count.val≤_; omega
end Positions

variable {G : Gauge} {C : Family G} {S : Table C.book} {d : ℕ} {X : Columns C S d} (Y : Tests X)
variable (h : G.Simple)
include h





-- Even deeper, no congestion. All actual copies. Ancestors before k.


omit h in
lemma crowd (k N p : ℕ) (hd : Y.B.depth k ≤ N) (m ℓ) (he : Y.B.side k ≤ m) (hf : m≤N) (i : Row X)
    (x : Site (C.side m p)) (s : Fin ℓ → Endpoint.Copies Y k p × Mark X i) (hi : Injective s)
    (hh : ∀ j, Flow.origin Y k N p i hd hf (s j)=x) : ℓ ≤ 2 := by
  have ht (j : Fin ℓ) : (C.S.toDepth he p).parent x = (s j).1 := by
    rw [← hh j]
    unfold Flow.origin
    rw [Positions.via_layers C.S he hf]
    exact Y.anchor k N p i (s j).2 hd (s j).1
  have h' : Injective (fun j => (s j).2) := fun i j h => hi (Prod.ext ((ht i).symm.trans (ht j)) h)
  exact le_trans ((Fintype.card_fin ℓ).symm.trans_le <| Fintype.card_le_of_injective _ h') (Last.dimension X i)
end YM.Push.Corrected.Progress
