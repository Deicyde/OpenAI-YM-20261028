import YM.FullVolume.Tess.Doric
import YM.FullVolume.Tess.Halo
/- performance Beam sequences and uniform all-compact hol interiors. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Tess
open Filter Function Set Metric MeasureTheory Lattice RG Ray Asymptotics
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
open Extraction Extraction.Lease Difference Amp Amp.Beam
variable {S:Schedule} {n N j m p:ℕ}{K K':Set (Points n)}
local notation "A"=>S.a
variable {U:ℕ→ Positions n→ Beam ℂ}{G: Points n→ Beam ℂ}(hk: Scroll S K U G)
namespace Scroll
include hk
lemma hatch {z:ℂ}(hv:z∈ optics): Scroll S K (fun i j=> heartX (U i j) z) (fun x=> heartX (G x) z):=by
    have h (X: Beam ℂ): heartX X z = haloC hv X:=rfl
    simp_rw [h]; refine ⟨(haloC hv).continuous.comp_continuousOn hk.land,fun ε he=>?_⟩
    filter_upwards [hk.wins ε he] with i hi y hy; rw [dist_eq_norm, ← map_sub]; exact (emitsN _ hv).trans_lt ((dist_eq_norm ..).symm.trans_lt (hi y hy))
lemma galaxy {J:Set ℂ} (hK:IsCompact K)(hJ:IsCompact J)(hv:J⊆optics)(d:ℕ):∀ ε:ℝ,0< ε→∀ᶠ i in atTop,∀ x:Positions n,tag (S.a i) x∈K→∀ z∈ J,dist (iteratedDeriv d (heartX (U i x)) z) (iteratedDeriv d (heartX (G (tag (S.a i) x))) z)< ε:=by
    intro ε he; by_contra! hx; obtain ⟨x,h,xH⟩:=extraction_of_frequently_atTop hx
    choose F hF z hz hh using xH
    let f i:=tag (S.a (x i)) (F i); obtain ⟨y,hy,u,hu,ht⟩:=hK.tendsto_subseq hF
    let T i:=x (u i); let S' i:=U (T i) (F (u i)); let C i:= G (f (u i))
    have hP:Tendsto S' atTop (𝓝 (G y)):= hk.retreat (v:=T) (h.tendsto_atTop.comp hu.tendsto_atTop) hy (Eventually.of_forall (fun i=>hF (u i))) ht
    have hY :Tendsto C atTop (𝓝 (G y)):= (hk.land y hy|>.tendsto).comp (tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall (fun i=>hF (u i))⟩)
    obtain ⟨i,hi,h⟩:= ((Metric.tendstoUniformlyOn_iff.mp (deluge S' hP _ hJ hv d) _ (half_pos he)).and (Metric.tendstoUniformlyOn_iff.mp (deluge C hY _ hJ hv d) _ (half_pos he))).exists
    let Z(X:Beam ℂ):=iteratedDeriv d (heartX X) (z (u i))
    have hc:dist (Z (G y)) (Z (S' i))< ε/2 :=hi _ (hz (u i)); rw [dist_comm] at hc
    have hb : dist (Z (G y)) (Z (C i))< ε/2:= h _ (hz (u i)); apply not_lt.mpr (hh (u i))
    apply (dist_triangle (Z (S' i)) (Z (G y)) (Z (C i))).trans_lt; linarith only [hc,hb]
-- conv.Beam from Seq for Reach after comp.N.
lemma restrict {V:Set (Points n)} (hv:V ⊆ K): Scroll S V U G:=⟨hk.land.mono hv,fun v p=> (hk.wins v p).mono (fun a ha x hx=> ha x (hv hx))⟩
end Scroll
section unify
variable {α:Type}{F:ℕ→α→Beam ℂ}{G:α→Beam ℂ}{K:Set α}
lemma merger [MetricSpace α] -- assume metric instead
   (hk:TendstoUniformlyOn F G atTop K) (hK:IsCompact K)(h:ContinuousOn G K)(J:Set ℂ)(hJ:IsCompact J)(hp:J⊆optics)(d:ℕ):∀ ε:ℝ,0<ε→∀ᶠ N in atTop,∀ i∈K,∀ z∈J,dist (iteratedDeriv d (heartX (F N i)) z) (iteratedDeriv d (heartX (G i)) z)< ε:=by
   intro ε he; by_contra! hx; obtain ⟨x,hx,xH⟩:=extraction_of_frequently_atTop hx; choose y hy z hz ht using xH
   obtain ⟨w,hW,p,P,hP⟩:= hK.tendsto_subseq hy
   let c i:= G (y (p i)); let t i:= F (x (p i)) (y (p i))
   have H:Tendsto c atTop (𝓝 (G w)):= (h w hW|>.tendsto).comp (tendsto_nhdsWithin_iff.mpr ⟨hP,Eventually.of_forall fun i=>hy (p i)⟩)
   have hv:Tendsto t atTop (𝓝 (G w)):=by apply H.congr_dist; refine Metric.tendsto_nhds.mpr (fun ε he=>?_); filter_upwards [(hx.tendsto_atTop.comp P.tendsto_atTop).eventually (Metric.tendstoUniformlyOn_iff.mp hk ε he)] with i hi; rw [dist_zero_right,Real.norm_of_nonneg dist_nonneg]; exact hi _ (hy _)
   obtain ⟨i,hi,hC⟩:= ((Metric.tendstoUniformlyOn_iff.mp (deluge c H _ hJ hp d) _ (half_pos he)).and (Metric.tendstoUniformlyOn_iff.mp (deluge t hv _ hJ hp d) _ (half_pos he))).exists
   let Z(X:Beam ℂ):=iteratedDeriv d (heartX X) (z (p i)); have hu:dist (Z (G w)) (Z (t i))< ε/2:=hC _ (hz _); have hg:dist (Z (G w)) (Z (c i))< ε/2:=hi _ (hz _); rw [dist_comm] at hu; exact not_le.mpr ((dist_triangle _ (Z (G w)) _).trans_lt ((add_lt_add hu hg).trans_eq (by ring))) (ht _)
end unify
end YM.FullVolume.Tess
#print axioms YM.FullVolume.Tess.Scroll.galaxy
#print axioms YM.FullVolume.Tess.merger
