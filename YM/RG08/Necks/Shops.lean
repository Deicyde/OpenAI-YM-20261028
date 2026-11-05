import YM.RG08.Necks.Epoch
/-! # Pair algebra mark rational receipts. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Skiff
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Flint Lagoon Yurt Next.Free
open scoped Classical ContDiff BigOperators Topology ENNReal
variable {I J:Type}{n m d p:ℕ}{σ τ μ V Q B C δ η a b W:ℝ}{L:Jetty.Loom I}{D:Jetty.Loom J}
variable {h:0<σ}{F F':Pack n I}
lemma Dyad.pure (hδ:0≤δ)(hB:0≤B)(he:Lyrics F)(hf:Sings L d h F B):Dyad L d h B δ F F:=⟨hB,hδ,⟨he,he⟩,hf,hf,by rw [sub_self];exact tin⟩ --
lemma Dyad.width (hs:Dyad L d h B δ F F')(ht:0<τ)(hp:τ ≤ σ):Dyad L d ht B δ F F':=⟨hs.price,hs.rate,hs.voices,hs.near.mono hp le_rfl (fun _=>le_rfl) le_rfl,hs.far.mono hp le_rfl (fun _=>le_rfl) le_rfl,hs.switch.mono hp le_rfl (fun _=>le_rfl) le_rfl⟩
lemma Dyad.livery (he:Dyad L d h B δ F F'){C:ℝ}(hA: |a| ≤ C)(hB: |b| ≤ C)(hc: |a-b|≤ C*δ): Dyad L d h (2*C*B) δ (a • F) (b • F'):=by
 obtain ⟨hP,hr,⟨hp,hq⟩,ht,hf,H⟩:=he;have hC:0≤C:=(abs_nonneg _).trans hA
 have hs(x:ℝ)(h:|x|≤ C): |x| * B≤2*C*B:=mul_le_mul_of_nonneg_right (h.trans (le_mul_of_one_le_left hC (by norm_num))) hP
 refine ⟨by positivity,hr,⟨hp.smul _,hq.smul _⟩,(ht.smul a).mono le_rfl le_rfl (fun _=>le_rfl) (hs a hA),(hf.smul b).mono le_rfl le_rfl (fun _=>le_rfl) (hs b hB),?_⟩ -- missing hr
 rw [show a • F-b • F' = a •(F-F')+(a-b) • F' from by rw [smul_sub,sub_smul];abel]
 apply ((H.smul _).add (hf.smul (a-b)) (by positivity) (by positivity)).mono le_rfl le_rfl (fun _=>le_rfl)
 calc
  _ ≤ C*(B*δ)+C*δ*B:= add_le_add (mul_le_mul_of_nonneg_right hA (by positivity)) (mul_le_mul_of_nonneg_right hc hP)
  _ =_:=by ring
lemma Dyad.minus (he:Dyad L d h B δ F F'){G T:Pack n I}(hg:Dyad L d h C δ G T):Dyad L d h (B+C) δ (F-G) (F'-T):=by
 have hf:= hg.smul (-1)
 rw [abs_neg,abs_one,one_mul, neg_smul,one_smul,neg_smul,one_smul] at hf
 rw [sub_eq_add_neg, sub_eq_add_neg];exact he.add hf
lemma Dyad.hike (he:Dyad L d h B δ F F')(h:δ≤τ):Dyad L d (by assumption : 0<σ) B τ F F':=⟨he.price,he.rate.trans h,he.voices,he.near,he.far,he.switch.mono le_rfl le_rfl (fun _=>le_rfl) (mul_le_mul_of_nonneg_left h he.price)⟩
lemma dyads_nil (he:Dyad L d h B 0 F F'):F=F':=by
 let N:=he.switch; rw [mul_zero] at N
 funext i u; apply sub_eq_zero.mp;apply abs_eq_zero.mp;apply le_antisymm _ (abs_nonneg _)
 have hz:=N.quote (he.voices.1.sub he.voices.2) le_rfl i u;rw [zero_mul] at hz;exact hz
end YM.RG08.Skiff
