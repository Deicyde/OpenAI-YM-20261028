import YM.RG08.Town.Ladle
/-!
# Moment transmission including untranslated true center distance variants
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Town
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series.Radial PertExtension.Series.Tested Pill Wings
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {I J:Type}{u : I→Windows}{w:J→ShoreP u}{X:Chain}{G:Gauge}{E e n r d τ D j k t ε:ℕ}{ν:G.ColorIndex}{F:Labels.Frame G d}{Ω:SectionData F}{H:Hol G}{D':ChartRatio G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}{R:ℝ}{h:1/2≤R}{hD:d+1≤D}{T:Signals P Q E τ H Ω h hD}{A:Grotto G P k E τ}
section bills
structure Pines (A:Grotto G P k E τ)(u:I→Windows):Prop where
   card : ∀ i:Launch u, A.gate (X.J (i.i+1)) ≤ (X.S.block i.i).val
lemma tappedL (p: Pines A u)(ht:Tights T S ν D' u)(i:Wings u 1)(z:Site (X.S.block i.i))(F:Rooted ℝ (Loc G 1) r)(hf:Tidy F)(h:r≠0)(hp:r≤ τ+E)(B v w:ℝ)(he:cis k w F B)(hv:0≤v)(hx:v≤1)(hk: v/(X.S.block i.i).val≤w): cis k v (holdP z (babyQ G X i) F) (B * gain X.S (1/2) i.i (i.i+1)):= by rw [gain_succ_half,mul_one_div]; exact A.receipt _ _ k r (X.flight i.N i.i) rfl h hp (X.adm _) (p.card i.toLaunch) z F hf B w v he hv hx hk
local notation "Ⓨ" => wallY X
local notation "Γ" => heights (u:=u) X ν D'
local notation "Λ" => strideP X
variable {y δ: Wall w 0→ℝ}{V:Wall w 1→ Tale G}{p q : J→ℝ} {W:Wall w 1→Wings u 1}{z:∀ i:Wall w 1,Site (X.S.block (W i).i)}
lemma curtain (he:Tights T S ν D' u)(hx : ∀ i,(W i).toLaunch=i.world.toLaunch)(hp:∀ i,Stone ε (V i))(hr:r≤ ε+e)(hδ:0≤δ)(hv:δ≤1)(hh :∀ i, δ (Wall.low (b:=w) i)/(X.S.block i.i).val ≤ δ i.roof)(hM:∀ i<e, ∀ r, Card k Ⓨ (Λ w p) (fun j:Wall w 1=> V j i r) (fun i=> δ i.roof)) : Card k Ⓨ (Λ w p) (fun i=>holdP (z i) (Γ (W i)).tree (V i e r) - holdP (z i) (babyQ G X (W i)) (V i e r)) (fun i=>δ i.low):= by
   obtain ⟨Z,hZ,H,hT,hV⟩:=walkerF (k:=k) he w W hx
   let p':=ε+e-r; let A i (j:Wall w 1):= Loom.strand ε p' (V j) i
   have hk i (hi:i∈range r): Card k Ⓨ (Λ w p) (A i) (fun i=>δ i.roof) := by
      unfold A Loom.strand; split; next h=> apply hM; have hh:=mem_range.mp hi; unfold p' at *; omega
      exact Card.zero
   have hy i (hi:i∈range r): Card k Ⓨ (Λ w p) (fun j=> belly (z j) (Z j) (crock (A i j) r)) (fun i=>δ i.low):= by
     obtain ⟨B,hB,H'⟩:= (hk _ hi).money; obtain ⟨C,hC,H⟩:= hZ; let b:= (((r+1:ℕ):ℝ)^k*silkSale G i r); have hb:0≤b:=mul_nonneg (by positivity) (silkSale_pos ..)
     refine ⟨_, ((Weighed.constant (wallY X (b:=w) (n:=1)) (show 0≤(1+4*(r:ℝ))^k by positivity)).times ((hT.times ((Weighed.constant Ⓨ (show 0≤(Fintype.card (Loc G 1):ℝ) by positivity)).times hC)).powers r)).times ((Weighed.constant Ⓨ hb).times hB),fun j=> Ink.raise (belly_exp_l (z j) (spun_p (H' j) (hδ j.roof) (hv j.roof)) (H j) (T.pos _) (mul_nonneg (hC.positive _) zero_le_one) (hδ j.low) (hv j.low) (?_ : δ j.low / (X.S.block (W j).i).val ≤ δ j.roof)) ?_⟩
     · rw [show (W j).i=j.i from congr_arg Launch.i (hx j)]; exact hh j
     exact le_of_eq (by unfold b; simp only [Pi.one_apply,mul_one,Pi.mul_apply,mul_assoc])
   have hu : Card k Ⓨ (Λ w p) (fun j: Wall w 1=> ∑ i ∈ range r, belly (z j) (Z j) (crock (A i j) r)) (fun i=>δ i.low):= Card.group _ (Wall.plusOne X) (fun i=>hδ i.low) hy
   convert hu.neg using 1; funext i
   have hp': V i e r = A r i:= by unfold A Loom.strand; rw [if_pos (by unfold p'; omega),show p'+r-ε=e by unfold p'; omega]
   rw [hp']; unfold A; rw [drapery (z i) (hp i) (hV i) (babyW (W i)) (he.fair (W i)|>.ct) (hZ.status (fun _=>T.pos _) _) p']; exact sub_sub_cancel_left ..
end bills
section scalar
variable {w : J→ShoreP u} {p v:J→ℝ}{A: Wall w 0→ Rooted ℝ (Loc G 1) 0}{z:Wall w 0→ℝ}
def badge (p:J→ℝ)(i:Wall w n):= p i.a
local notation "Ⓨ" => wallY X
lemma tail0 (p v:ℝ){X' :Rooted ℝ (Loc G 1) 0}{A:ℝ}(h:cis k p X' A): cis k v X' A:= by change Quire.Ink (tailP k v) X' A; rw [show (tailP k v:Beads (Loc G 1) 0→ℝ)= tailP k p from funext fun i=> by simp [tailP,girth]]; exact h
lemma signify (ht:Card k (fun i=>Ⓨ (Wall.tip w i)) p (fun i=> A (Wall.tip w i)) (fun i=> z (Wall.tip w i)))(hp:0≤p)(hz:0≤z)(h:Card k Ⓨ (badge p) (fun i:Wall w 1=> A i.low-A i.roof) (fun i=>z i.low)) : Card k Ⓨ (badge p) A z:= by
   obtain ⟨U,⟨B,n,hB,H⟩,hU⟩:=ht.money; obtain ⟨Q,⟨C,m,hC,hQ⟩,Hu⟩:=h.money
   let M t:=(w (Wall.a (b:=w) (n:=0) t)).city; let Y:= wallY (b:=w) (n:=0) X; have hv:Weighed Y (fun i=> (M i:ℝ)):= (subsegment (u:=_) X).transfer (fun i:Wall w 0=>w i.a)
   refine ⟨_,((Weighed.constant Y hB).times (Weighed.power _ (Wall.plusOne X) n)).plus ((hv.times (Weighed.constant Y hC)).times (Weighed.power _ (Wall.plusOne X) m)) (Wall.plusOne X),fun i=>?_⟩
   let t:=Wall.tip w i.a; let N:=t.i; let b:=(w i.a).low; let y:= Y i; have ht: 1≤y:= Wall.plusOne X _; let q:= p i.a; have hp:0≤q:=hp _; let u:= C*y^m; have hh:0≤u:=mul_nonneg hC (by positivity)
   let W n (h:b≤n) (ht:n≤N): Wall w 0:=⟨i.a,n,h,ht⟩
   have hv j (he:j≤ N)(hk:b≤j): cis k (z (W j hk he)) (A (W j hk he)) ((B*y^n+ (↑(N-j):ℝ)*u)*q) := by
     induction he using Nat.decreasingInduction with
     | self=> simp only [tsub_self,Nat.cast_zero,zero_mul,add_zero]; exact Ink.raise (hU i.a) (mul_le_mul_of_nonneg_right (H i.a|>.2) hp)
     | of_succ j hj ih=>
       let s: Wall w 1:= ⟨i.a,j,hk,hj⟩; have ht':= ih (hk.trans (Nat.le_succ _)); have he: cis k (z s.low) (A s.low-A s.roof+A s.roof) _ := Ink.plus (Hu s) (tail0 (z s.roof) (z s.low) ht') (zero_le_one.trans (tailp (hz s.low)))
       rw [sub_add_cancel] at he; apply Ink.raise he
       apply le_trans (add_le_add_left (mul_le_mul_of_nonneg_right (show Q s ≤ u from (hQ s).2) hp) _) (le_of_eq ?_)
       rw [show N-j=N-(j+1)+1 by omega]; push_cast; ring
   have hh' := hv i.i i.last i.first; apply Ink.raise hh'
   change _ ≤ (B*y^n+(↑(M i):ℝ)*C*y^m)*q
   rw [mul_assoc (↑(M i):ℝ)]; exact mul_le_mul_of_nonneg_right (add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (show N-i.i≤N-b from by have he:b≤ i.i:=i.first; omega)) hh) _) hp
end scalar
end YM.RG08.Town
