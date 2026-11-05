import YM.RG08.Bands.Tongs
/-!
# Ratios at orientations and royal visits to first join
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Bands
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {I :Type}{α:I→Type}{n k b r s:ℕ}{η y v p q x c δ ρ σ : I→ℝ}{z u:I→Cover}
section braid
variable {F H:∀ i, Shale (α i) r}{Q K:∀ i,Shale (α i) s}
lemma card_r (hf:Card (k+b) y δ F p)(hw:0≤p): Card k y δ F p:= by
   obtain ⟨A,hA,H⟩:=hf.money; refine ⟨_,hA,fun i=> Ink.shrink (H i) (zero_le_one.trans (tailp (hw i))) (fun z=> pow_le_pow_right₀ (by dsimp only; have he:=hw i; change 1≤1+p i*girth z; exact le_add_of_nonneg_right (mul_nonneg he (by positivity))) (Nat.le_add_right k b))⟩
lemma roam_card (hf:Card k y δ F 1)(hp:0≤η)(ht:η≤1)(hv:Weighed y (fun i=>η i*size (z i)))(he:Audience y): Card k y δ (fun i=>roam (z i) (F i)) η:= by
   obtain ⟨A,hA,H⟩:=hf.money
   refine ⟨_, (((Weighed.one (y:=y)).plus ((Weighed.constant y (Nat.cast_nonneg r)).times hv) he).powers k).times hA,fun i=> ?_⟩
   have hx:cis k (η i) (F i) (A i*δ i):= Ink.shrink (H i) (zero_le_one.trans (tailp (hp i))) (fun j=> pow_le_pow_left₀ (by have he: 0 ≤ η i:=hp i; positivity) (add_le_add_right (mul_le_mul_of_nonneg_right (ht i) (Nat.cast_nonneg _)) _) _) -- Lean tail unfolding
   refine Ink.raise (roam_cis hx (hp i) (z i)) (le_of_eq ?_); simp only [Pi.mul_apply,Pi.add_apply,Pi.pow_apply,Pi.one_apply]; ring
lemma roam_enough (h:Drum (k+b) y δ ρ F H 1)(hp:0≤η)(ht:η ≤ 1)(hv:Weighed y (fun i=>η i*size (z i)))(he:Audience y): Drum k y δ ρ (fun i=>roam (z i) (F i)) (fun i=>roam (z i) (H i)) η:= ⟨roam_card (card_r h.first zero_le_one) hp ht hv he,roam_card (card_r h.second zero_le_one) hp ht hv he,roam_card (card_r h.funds zero_le_one) hp ht hv he⟩ -- defeq F−H
lemma knot_b (h:Card k y p F η)(he: Card k y q Q η)(hp:0≤η): Card k y (p*q) (fun i=>braidV (F i) (Q i)) η:= by
   obtain ⟨A,hA,H⟩:=h.money; obtain ⟨U,hU,V⟩:=he.money; exact ⟨_,hA.times hU,fun i=> Ink.raise (braid_pol (H i) (V i) (hp i)) ((mul_mul_mul_comm ..).le)⟩
lemma knotted (h:Drum k y δ p F H η)(he:Drum k y δ q Q K η)(hp:0≤η)(hv:Audience y): Drum k y δ (p*q) (fun i=>braidV (F i) (Q i)) (fun i=>braidV (H i) (K i)) η := by
   let X i:=braidV ((F-H) i) (Q i); let Y i:=braidV (H i) ((Q-K) i)
   refine ⟨knot_b h.first he.first hp,knot_b h.second he.second hp,?_⟩
   rw [show _-_ = X+Y from funext fun i=>by simp only [X,Y,Pi.sub_apply,Pi.add_apply]; rw [braid_l (h.first.even hp i) (h.second.even hp i) (he.first.even hp i),braid_b (he.first.even hp i) (he.second.even hp i) (h.second.even hp i)]; abel]
   rw [←mul_assoc]; refine (knot_b h.funds he.first hp).more (U:=X) ?_ hp hv
   rw [mul_assoc,mul_left_comm]; exact knot_b h.second he.funds hp
end braid
section precious
variable {F H:∀ i, Shale (α i) (r+1)}{Q K:∀ i, Shale (α i) (s+1)}{P V:∀ i,Row (α i) (α i)}
-- charge any finite power of true path length on ONE contact
lemma precious (hy:Audience y)(hz:0≤η)(hv:η≤1)(hδ:0≤σ)(hc:0≤c) (hu:Weighed y (fun i=>η i*size (z i)))(hh: Weighed y (fun i=>η i*size (u i)))(he:Card (k+b) y p F 1)(hp:Card (k+b) y q Q 1)(h:SafeRow y c P v)(hx:∀ i,0<v i)(hg:Weighed y (fun i=>Run.utter b (v i)))(hB:Weighed y x)(hX:∀ i,1 ≤ x i*σ i*(1+(size (z i-u i):ℝ))) : Card k y (c*p*q*σ^b) (fun i=>countP none (P i) (roam (z i) (F i)) (roam (u i) (Q i))) η:= by
   obtain ⟨A,hA,H⟩:=he.money; obtain ⟨B,HP,W⟩:=hp.money; obtain ⟨C,hC,Z⟩:=h
   let D (z:I→Cover)(r:ℕ)(i:I):= (1+((r+1:ℕ):ℝ)*(η i*size (z i)))^k
   have hy' (z:I→Cover)(u:Weighed y (fun i=>η i*size (z i))) r: Weighed y (D z r):= ((Weighed.one (y:=y)).plus ((Weighed.constant _ (Nat.cast_nonneg (r+1))).times u) hy).powers k
   refine ⟨_,(((Weighed.constant y (norm_nonneg (syl r s))).times (hy' z hu r)).times (hy' u hh s)).times ((hB.powers b).times ((hg.times hC).times (hA.times HP))),fun i=>Ink.raise (count_l (H i) (W i) (Z i) (hx i) (mul_nonneg (hC.positive _) (hc _)) (hz i) (hv i) (hX i) (mul_nonneg (hB.positive _) (hδ _))) (le_of_eq ?_)⟩
   simp only [Pi.mul_apply,D,Pi.pow_apply,mul_pow]; ring
private lemma count_minus {α:Type}{K P:Row α α}{U:Shale α (r+1)}{V:Shale α (s+1)}(h:Pens U)(ht:Pens V)(he:Whole K)(hp:Whole P): countP none (K-P) U V=countP none K U V-countP none P U V:= by
   unfold countP; rw [show interU U V*bob none (K-P)=interU U V*bob none K-interU U V*bob none P from funext fun i=>mul_sub ..,Pens.tub_sub _ (bob_pens h ht he) (bob_pens h ht hp),smul_sub,sew_sub]
lemma bonfire (hy:Audience y)(h:0≤η)(hz:η≤1)(ht:0≤δ)(hS:0≤σ)(hu:Weighed y (fun i=>η i*size (z i)))(hh:Weighed y (fun i=>η i*size (u i))) (he:Drum (k+b) y δ p F H 1)(hp:Drum (k+b) y δ q Q K 1)(hP:RowBoth y δ P V v)(hx:∀ i,0<v i)(hg:Weighed y (fun i=>Run.utter b (v i)))(hB:Weighed y x)(hX:∀ i,1≤ x i*σ i*(1+(size (z i-u i):ℝ))) : Drum k y δ (p*q*σ^b) (fun i=> countP none (P i) (roam (z i) (F i)) (roam (u i) (Q i))) (fun i=> countP none (V i) (roam (z i) (H i)) (roam (u i) (K i))) η := by
   have h1 : (0:I→ℝ)≤1:= zero_le_one; let f T (U:∀ i,Shale (α i) (r+1)) W:= fun i=> countP none ((T:∀ i,Row (α i) (α i)) i) (roam (z i) (U i)) (roam (u i) ((W:∀ i,Shale (α i) (s+1)) i))
   have hW : f P F Q-f V H K=f (P-V) F Q+f V (F-H) Q + f V H (Q-K):= by
     funext i; have hR:=pens_roam (he.first.even h1 i) (z i); have hy':=pens_roam (hp.first.even h1 i) (u i); have hw: Whole (V i):= hP.again.status hx i
     simp only [Pi.sub_apply,Pi.add_apply,f,Town.roam_less]; rw [count_minus hR hy' (hP.fresh.status hx i) hw, county_left hR (pens_roam (he.second.even h1 i) _) hy' hw,county_right hy' (pens_roam (hp.second.even h1 i) _) (pens_roam (he.second.even h1 i) _) hw]; abel
   have ha(k:ℕ)(b:ℕ)(σ' p q c:I→ℝ)(hB':Weighed y (fun i=>Run.utter b (v i)))(hc:0≤c)(P U V)(he:Card (k+b) y p U 1)(hv:Card (k+b) y q V 1)(h:SafeRow y c P v): Card k y (c*p*q*σ^b) (f P U V) η:= precious hy ‹0≤η› hz hS hc hu hh he hv h hx hB' hB hX
   have he' v:=ha k b σ p q 1 hg h1 v F Q he.first hp.first -- expecting ∀ v Spec
   change Drum _ _ _ _ (f P F Q) (f V H K) η
   refine ⟨?_,?_,?_⟩
   · simpa only [one_mul] using he' P hP.fresh
   · simpa only [one_mul] using ha k b σ p q 1 hg h1 V H K he.second hp.second hP.again
   rw [hW,← mul_assoc,←mul_assoc]; refine ((ha k b σ p q δ hg ht _ F Q he.first hp.first hP.moves).more ?_ h hy).more ?_ h hy
   · simpa only [one_mul] using ha k b σ (δ*p) q 1 hg h1 _ _ _ he.funds hp.first hP.again
   convert ha k b σ p (δ*q) 1 hg h1 _ _ _ he.second hp.funds hP.again using 1
   simp only [one_mul,mul_assoc,mul_left_comm δ p]
end precious
end YM.RG08.Bands
