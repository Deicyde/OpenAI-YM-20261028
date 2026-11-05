import YM.RG05Readout.Address.Snap
/-!
# Combining snapshot prices

Proves every linear operation used in aligned Snap with exact common labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G: Gauge}{n:Side}{d e k:ℕ} {F:Labels.Frame G d}{T:Labels.Frame G 0}{X:SectionData T}{Z:SectionData F}{A:Hol G}{R:Rep G n}{o:Site n}{c v w t u a b η κ σ Λ C δ w' : ℝ}{P Q:Tape G n}
namespace Necklace
variable (h:Necklace T X A R o κ d P c)
include h
lemma nonneg : 0≤c:= by induction h with
   | empty=>exact le_rfl
   | chain f _ hr x hf he _ ih=> exact add_nonneg (mul_nonneg (Priced.nonneg _ hr) (add_nonneg (Work.G08.size_nonneg ..) (rem_nonneg he))) ih
lemma plus (hh:Necklace T X A R o κ d Q t):Necklace T X A R o κ d (P+Q) (c+t):=by induction h with
   | empty=>simpa only [zero_add] using hh
   | chain z hv h a ha hw _ ih=> simpa only [add_assoc] using (chain z hv h a ha hw ih)
lemma scaled (z:ℂ) : Necklace T X A R o κ d (z • P) (‖z‖*c):=by induction h with
   | empty=>simp [empty]
   | chain f hz h a hp he ht ih=>
        have hh:= chain f hz h (stretch z a) (stretch_format z hp) (stretch_rem z he) ih
        rw [invoice_stretch,glyph_stretch,show (stretch z a).x=z • a.x from rfl,Size.smul, ← mul_add,mul_left_comm] at hh
        rw [smul_add,mul_add]; exact hh
lemma works (hr:R.Lawful σ C Λ δ w) (φ:Body): Useful R (P φ):=by induction h with
    | empty=> exact Useful.zero R
    | chain f _ hk u hu he ht ih=> exact Useful.join R hr (Useful.smul R _ _ (Useful.invoice _ _ _ R hr he hu)) ih -- maybe arguments
lemma vanishes (i:Letter d):P (line i)=0:=by induction h with
    | empty=> rfl
    | chain v hx hh f hu he ht ih=> rw [LinearMap.add_apply,glyph_apply,hx i,zero_smul,ih,add_zero]
end Necklace
variable {C:Family G}{x y x' y': Palette C d}
set_option quotPrecheck false
open Trace.Physical
local notation "G₀"=> C.labels.level
local notation "Y₀"=> C.localSection
-- exact supplied operations
lemma together_line (S:lows C n d)(g:Tape G n)(hh:Necklace (C.labels.level 0) (C.localSection 0) C.params R o κ d g t)(i:Letter d):
     (together C R o d S+g) (line i)= invoice (S i) o (Y₀ (kept i)) R:=by
    rw [LinearMap.add_apply,hh.vanishes,add_zero, together,LinearMap.sum_apply]; simp_rw [glyph_apply,headC,ite_smul]; simp
lemma perspective (Y:Hol G){P:Coefficient F n}(z: ℂ) (hP:P.Format o Y R)(hd:d≤R.p.order)(hp:d≤R.p.power)(he:P.remBound o R v w): Trace.Physical.Germ.projection F Y R.p.threshold o (stretch z P) = z • Trace.Physical.Germ.projection F Y R.p.threshold o P:=by
   let g:ℂ → Coefficient F n:=fun α => stretch α P
   have hu:IsLinearMap ℂ (fun c=>(g c).regular):= ⟨fun _ _=> add_smul ..,fun _ _=> smul_assoc ..⟩
   have hQ:IsLinearMap ℂ (fun i=> Trace.Physical.Germ.projection F Y R.p.threshold o (g i)) := Trace.Physical.Germ.linear_projection F Y g hd hp (fun _=>stretch_format _ hP) (fun _=>⟨_,_,stretch_rem _ he⟩) ⟨⟨fun _ _=>add_smul ..,fun _ _=> smul_assoc ..⟩,hu⟩
   have h1:g 1=P:= by unfold g Extra.Histories.stretch; simp
   exact (congr_arg (fun i=>Trace.Physical.Germ.projection F Y R.p.threshold o (g i)) ((mul_one z).symm)).trans (((hQ.map_smul z (1:ℂ))).trans (by rw [h1]))

namespace Printed
variable (h: Printed C d R o κ P x y c)
include h
lemma grow (ht:c ≤ b): Printed C d R o κ P x y b:= by obtain ⟨P,F,H,h,hS,he,hx,hy,hp⟩:=h; exact bind P F H h hS he hx hy (hp.trans ht)
lemma nonneg :0≤ c:=by
    obtain ⟨P,F,H,h,hS,he,hx,hy,hp⟩:=h; exact (add_nonneg (Finset.sum_nonneg fun i _=>rem_nonneg (hS i)) H.nonneg).trans hp
lemma useful (hr:R.Lawful σ a Λ δ w)(φ:Body): Useful R (P φ):=by
    obtain ⟨S,H',H,hF,hS,rfl,hx,hy,hp⟩:=h; rw [LinearMap.add_apply,together, LinearMap.sum_apply]
    exact Useful.join R hr (Useful.family R hr _ _ (fun i=>Useful.smul R _ _ (Useful.invoice _ _ _ R hr (hS i) (hF i)))) (H.works hr _)
lemma addP (hw:Printed C d R o κ Q x' y' t)(hr:R.Lawful σ a Λ δ w)(hk:d ≤ R.p.order)(hz:d ≤ R.p.power): Printed C d R o κ (P+Q) (x+x') (y+y') (c+t):=by
    rcases h with @⟨V,F,v,b,H,h,hp,rfl,rfl,rfl,hc⟩; rcases hw with @⟨T,K,w,u,W,f,hf,rfl,rfl,rfl,ht⟩
    let S(i):= beside (V i) (T i); refine bind S (F+K) (H.plus W) (fun i=>(presentation (h i) (hp i) (f i) (hf i)).1) (fun i=>(presentation (h i) (hp i) (f i) (hf i)).2) ?_ (funext (fun i=>(reckon _ _).symm)) ?_ ?_
    · have he: together C R o d S=together C R o d V+together C R o d T:=by
          unfold together S; simp_rw [fun i=> invoice_add (V i) o (Y₀ (kept i)) R (T i) hr (hp i) (hf i), glyph_plus, Finset.sum_add_distrib]
      rw [he]; abel
    · exact funext fun i=> Eq.symm (Trace.Physical.GermGraph.add_projection (kept i) (V i) (T i) (h i) (f i) ((Nat.sub_le ..).trans hk) ((Nat.sub_le ..).trans hz) ⟨_,_,hp i⟩ ⟨_,_,hf i⟩)
    rw [Finset.sum_add_distrib, add_add_add_comm]; exact add_le_add hc ht
lemma twist (hk:d ≤ R.p.order)(hz:d ≤ R.p.power) (z:ℂ): Printed C d R o κ (z • P) (z • x) (z • y) (‖z‖*c):=by
    rcases h with @⟨V,F,v,b,H,h,hp,rfl,rfl,rfl,hc⟩
    let S(i):=stretch z (V i)
    refine bind S _ (H.scaled z) (fun i=>stretch_format z (h i)) (fun i=>stretch_rem z (hp i)) ?_ rfl ?_ ?_
    · have he : together C R o d S=z • together C R o d V:=by unfold together S; simp_rw [invoice_stretch,glyph_stretch, Finset.smul_sum]
      rw [he,smul_add]
    · exact funext fun i=> (perspective C.params z (h i) ((Nat.sub_le ..).trans hk) ((Nat.sub_le ..).trans hz) (hp i)).symm
    rw [← Finset.mul_sum, ← mul_add]; exact mul_le_mul_of_nonneg_left hc (norm_nonneg _)
omit h in
lemma blank (hκ:0 < κ):Printed C d R o κ 0 0 0 0:=by
    let V(i:Letter d):Coefficient (C.labels.level (kept i)) n:= Extra.Histories.primary o 0
    let s:= Necklace.empty (G:=G) (R:=R) (κ:=κ) (s:=d) (o:=o) (T:=G₀ 0) (Z:=Y₀ 0) (H:=C.params)
    refine bind (V) 0 s (fun _=> primary_format _) (fun _=> primary_rem _ hκ) ?_ rfl ?_ (by simp)
    · unfold together V; simp_rw [invoice_zero,glyph_zero]; simp
    funext i; have hv l: Trace.Physical.Germ.vector (G₀ (kept i)) C.params R.p.threshold o ((V i).regular l)=0:=by
       unfold V Trace.Physical.Germ.vector; simp only [Extra.Histories.primary, Pi.zero_apply]
       rw [show Trace.Physical.Germ.label C.params o (0:Config G n→ℂ) (kept i)=0 from ?_,map_zero,map_zero]
       unfold Trace.Physical.Germ.label; split; next h=>
          apply Next.Foundations.JetTest.unique h.choose_spec
          apply (Next.Foundations.jetTest_zero_iff ..).mpr
          exact fun j=>⟨contDiffAt_const,fun k _=> by simp⟩
       next=> rfl
    simp_rw [Trace.Physical.Germ.projection,hv,tsum_zero,add_zero];rfl
omit h in
lemma all {ι:Type*}(hκ:0 < κ)(hr:R.Lawful σ a Λ δ w)(S:Finset ι){t:ι→ℝ}{u v:ι→Palette C d}{J:ι→Tape G n}(hk:d≤R.p.order)(he:d≤R.p.power)(hf:∀ i∈S, Printed C d R o κ (J i) (u i) (v i) (t i)):
     Printed C d R o κ (∑ i∈ S,J i) (∑ i∈ S,u i) (∑ i∈ S,v i) (∑ i∈ S,t i):=by
       induction S using Finset.induction with
       | empty=> simp only [Finset.sum_empty]; exact Printed.blank hκ
       | insert i s hx ih=> simp_rw [Finset.sum_insert hx]; exact addP (hf _ (Finset.mem_insert_self ..)) (ih (fun i hi=> hf i (Finset.mem_insert_of_mem hi))) hr hk he

-- intrinsically computes the coupled test/field jet in the pinned projection convention
lemma survives (hw: Printed C d R o κ Q x' y' u) (hY:∀ (i:Letter d), ∃ w:ℝ, Readable C.params (C.localSection (kept i)) R.p n w)(he:∀ (i:Letter d),(P (line i)).1=ᶠ[𝓝 1](Q (line i)).1): y=y':=by
    rcases h with @⟨V,F,v,b,H,h,hp,rfl,rfl,rfl,hc⟩; rcases hw with @⟨T,K,w,u,W,f,hf,rfl,rfl,rfl,ht⟩
    funext i; obtain ⟨e,hE⟩:=hY i; let d':=kept i
    apply Trace.Physical.Germ.intrinsic_at (G₀ d') C.params (Y₀ d') hE.sound o hE.fit hE.order hE.power _ (V i) (T i) (h i) (f i) ⟨_,_,hp i⟩ ⟨_,_,hf i⟩
    · have hz:=he i; rw [together_line V F H,together_line T K W] at hz; exact hz
    intro g
    have ha:=presented_good o hE ((G₀ d').scaled R.p.threshold g)
    have h1 : presented (Y₀ d') o R.p.threshold ((G₀ d').scaled R.p.threshold g)= (Y₀ d').places g o:=by
       unfold presented; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; congr 2
       simpa using (G₀ d').scaled_inv (inv_ne_zero R.p.threshold_pos.ne') g
    rw [h1] at ha
    exact (ha.1.smooth 1 (Next.Foundations.one_healthy _ _ R.p.threshold_pos.le)).of_le (Nat.cast_le.mpr hE.order)
end Printed
end YM.RG05Readout.Address
