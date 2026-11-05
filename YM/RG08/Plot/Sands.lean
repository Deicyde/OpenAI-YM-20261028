import YM.RG08.Plot.Atelier
/-!
# Drop profiles with power gain paid at first joins on every sector. Keep the common orientation and admitted census.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Plot
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town Bands
open scoped BigOperators Topology Real ContDiff -- with domain Fintype Pi later
variable {I J M:Type} {L:I→ Side}{r n k E D τ j b:ℕ}{a ℓ:I→ℕ}{G:Gauge}{X:Chain}{R:ℝ}{y δ w v η C B:I→ℝ}{P Q :∀ i,StripU G (L i)}
section exposure
lemma drum_w (h:LensP k E τ y δ w P Q)(b:J→I) : LensP k E τ (y∘b) (δ∘b) (w∘b) (fun i=> P (b i)) (fun i=>Q (b i)) := by
    refine ⟨fun i=> h.one (b i),fun i=>h.two (b i),fun _=>h.age _,h.pay.transfer b, RG08.RowBoth.mold h.art b, RG08.RowBoth.mold h.meanT b,fun e he t ht r=> RG08.Both.mold (h.chargesG _ he _ ht r) b,fun e he=> Summit.Lease.whirls (h.scaleT _ he) b,fun _ => h.pos _,h.owns.transfer b,fun _=> h.rent _⟩ -- rg08 name
variable {x:I→ E4}{φ:J→I→Profile D}{u:List J}{s:J→I→ℝ}
structure Mats (u:List J)(y C B:I→ℝ)(s:J→I→ℝ)(φ:J→I→Profile D): Prop where
   spanH : Weighed y C
   bill : Weighed y B
   zero i (hi:i∈u): 0≤s i
   space i (hi:i∈u) t : Spatial (φ i t).val (C t)
   mass i (hi:i∈u) t: Reads (φ i t).val (s i t)
   split i (hi:i∈u) j (hj:j∈u) t: i≠ j → Resolve (φ i t).val (φ j t).val (B t)
-- incoming always probed finer than k
variable (X a ℓ)
local notation "⧈" => WidthP X a ℓ
lemma spinTick (h:Audience y)(hp: Weighed y (fun i=> ((X.S.block (ℓ i)).val:ℝ)))(ht:⧈≤1): (WidthP X a (fun i=>ℓ i+1)) ≤ 1:= by
   intro i; let P:= spanP X (a i) (ℓ i+1); have hL : 1 ≤ ((X.S.block (ℓ i)).val:ℝ) := by exact_mod_cast (X.S.block (ℓ i)).property
   apply le_trans (b:=⧈ i) ?_ (ht i); unfold WidthP; rw [← spanP_tick X (a i) (ℓ i)]; exact le_mul_of_one_le_right (spanP_pos ..|>.le) hL -- nth
variable {X a ℓ}
abbrev noses (X:Chain) (i:I)(a ℓ:I→ℕ)(g:I→Profile D)(x:I→E4)(R:ℝ):= blush (g i) X (a i) (ℓ i+1) (x i) R
variable {g:I→Profile D}{z:J→I→Cover}
local notation "⧉" => WidthP X a ℓ
lemma p_weight (h:1/2≤R)(hp:Audience y)(hM:Mats u y C B s φ)(i:J)(hi:i∈u)(hK:⧉ ≤1) (hz:∀ i'∈u,∀ j,z i' j∈ noses X j a ℓ (φ i') x R): Weighed y (fun j=>⧉ j * size (growP (X.S.block (ℓ j)) (z i j)-arcT X (a j) (ℓ j) (x j)) ) := by
    have he(j:I) : reached (φ i j).val (x j) (spanP X (a j) (ℓ j+1)) R (z i j):= blush_v.mp (hz i hi j)
    exact summited (g:=φ i) (R:=R) ((by norm_num : (0:ℝ)≤1/2).trans h) hp hM.spanH (hM.space i hi) (fun j=>blush_v.mpr (descendant h (he j))) hK
lemma leaves_from (h:1/2≤R) {P Q:∀ i,StripU G (X.S.block (ℓ i))} (he:LensP b E τ y δ v P Q)(hh:⧉ ≤1)(hM:Mats u y C B s φ)(hz:∀ j∈u,∀ i,z j i ∈ noses X i a ℓ (φ j) x R) :
   Leaves b u (fun j i=> growP (X.S.block (ℓ i)) (z j i)-arcT X (a i) (ℓ i) (x i)) y (WidthP X a ℓ) (WidthP X a ℓ) v δ (fun t=> B t*(1+8*R)) (fun i=>veiled (P i).cv) (fun i=>veiled (Q i).cv):= by
   have ht(i):0≤⧉ i:=spanP_pos ..|>.le; have hp:(0:ℝ)≤R:=le_trans (by norm_num : (0:ℝ) ≤1/2) h
   refine ⟨he.age,ht,hh,he.rent,fun i hi=> p_weight h he.age hM i hi hh hz,hM.bill.times (Weighed.constant _ (show 0≤1+8*R by positivity)),?_,ht,veil_contract he.art he.rent,he.pos,he.owns⟩
   intro i hi j hj hu k
   rw [sub_sub_sub_cancel_right]; exact outskirt (descendant h (blush_v.mp (hz i hi k))) (descendant h (blush_v.mp (hz j hj k))) (hM.split i hi j hj k hu) (hM.bill.positive k) (ht k)
lemma mats_hood (h:Mats u y C B s φ)(b:M→I): Mats u (y∘b) (C∘b) (B∘b) (fun i=> s i∘b) (fun i=>φ i∘b):= ⟨h.spanH.transfer b,h.bill.transfer b,fun i hi _=> h.zero i hi _,fun i hi _=> h.space i hi _,fun i hi _=>h.mass i hi _,fun i hi j hj t=>h.split i hi j hj _⟩
end exposure
end YM.RG08.Plot
