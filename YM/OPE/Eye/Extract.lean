import YM.OPE.Eye.Fast
/-!
# Extract matching bounds
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
set_option quotPrecheck false
open Function Filter Set Lattice RG Wilson MergeProof Accent Ribbons Source Overlay
open Bid ManyCopies Spec Extraction
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{F: Extraction.Order}{S:Table C.book} (U:Final C F S) {I J L : Type}[Fintype I][Fintype J] {φ:Filter L} [φ.NeBot] {T A p : L→ℝ}{b c d e q r s δ : ℝ}
variable {v k m n l j: L→ℕ}{u:L→I→ Cover} (x:I→ C.book.Token)(y:J→ C.book.Token) {X:L→I→ E4}{Y:L→J→ E4}(hT:Tendsto T φ atTop)
local notation "w"=> (fun i=> C.S.gridPoint (j i) ∘ u i)
include hT
lemma terrain (hG:G.Simple){W r D} (L': Package C W r D)[DecidableEq I] (hk:Height C.S φ T k b)(hm:Height C.S φ T m c)(hj:Height C.S φ T j d) (hb:b<c)(hc:c<e)(hd:e<d)
    (hX:extentWithin φ T (fun i=>C.S.gridPoint (j i) ∘ u i) e)(hY:Kept φ T e (fun i=>C.S.gridPoint (j i) ∘ u i)) : ∀ᶠ i in φ, Plot C (k i) (m i) (j i) (u i):=by
    have hp:=hm.step C.path.levels.fits.mesh; have hx:= (height0 (briar C hG L'.accounting) hj|>.power 2); have hv:=(hp.mesh.div (RateIs.const (c:=8*2) hT (by norm_num))).outweigh hX (by linarith) hT
    have hh:=hY.short hd hT ((((Moment_gap hT hj hd).mul (hx.pays hT)).mono (by simp)))
    filter_upwards [hv,hh,hk.earlier hb hT hm,hp.earlier (hc.trans hd) hT hj] with i hv hh hi he; refine ⟨fun j'=>?_,hh,hi.le,he.le⟩; have he:= (norm_le_pi_norm (w i) j').trans hv; dsimp only [comp_apply] at he; linarith only [he,C.S.a_pos (m i+1)];

include U
local notation "Z'"=> ((sigma x:ℕ):ℝ)*d+4*(Fintype.card I:ℝ)*(d-c)
variable {t:ℕ}
lemma for_plot [DecidableEq I] (i₀:I)(hG:G.Simple){W r D} (L': Package C W r D) (hk:Height C.S φ T k b)(hm:Height C.S φ T m c)(hj:Height C.S φ T j d) (hb:b<c)(hc:c<e)(hd:e<d)(t:ℕ)
    (hX:extentWithin φ T (fun i=>C.S.gridPoint (j i) ∘ u i) e)(hY:Kept φ T e (fun i=>C.S.gridPoint (j i) ∘ u i)) :
    ∃ A p : L→ℝ, ∃ Q:L→ C.label t, RateIs φ T p ((Z')-t*c) ∧ RateLE φ T A ((Z')-(t+1/16)*(c-b)) ∧ ∀ᶠ i in φ, Survival (C:=C) F (k i) (m i) (j i) (A i) (p i) x (u i) t (Q i) :=by
    obtain ⟨g,o,H,h,-,hv⟩:= funding (l:=φ) i₀ hG L' U.room.cutoff (fun i=>(x i).1) (fun i=>(x i).2) t hk hm hj hT hb (hc.trans hd) (height_room hk hm hT hb _)
    let V i (q:C.label t):= Survival (C:=C) F (k i) (m i) (j i) (o i) (g i) x (u i) t q
    let Q i:= if h:∃ q,V i q then Classical.choose h else 0
    refine ⟨o,g,Q,H,?_,?_⟩; · apply h.mono; unfold sigma; linarith only
    filter_upwards [terrain hT hG L' hk hm hj hb hc hd hX hY,hv] with i hx hv; rw [show Q i=_ from dif_pos (price_plot U (v:=x) hv hx)]; exact Classical.choose_spec _

variable {P: L→ C.label t} {g:I→ C.book.Token}{h:Org.Grill C F}
local notation "D" => (fun i=> sole (⟨t,P i⟩ : C.book.Token))
local notation "R" => (fun i=> viewing U (beside (w i) (Y i)) (beside g y) - viewing U (beside (sole (0:E4)) (Y i)) (beside (D i) y))
-- exterior budgets may require d not fixed, introduce new rates b(main support),a ext clearance, u general cost alias
variable (hS:∀ᶠ i in φ, Survival (C:=C) F (k i) (m i) (j i) (A i) (p i) g (u i) t (P i))
    (hG: ∀ᶠ i in φ, Screen (C.S.gridPoint (j i) ∘ u i))
    (hΓ: ∀ᶠ i in φ, Injective (beside (C.S.gridPoint (j i) ∘ u i) (Y i)))
    (hA:RateLE φ T A δ)
    (hF:Height C.S φ T k b)(hJ:Height C.S φ T j d)(hb:b<d)
    (hp:Intervals φ T c (centerless L) Y)(he:Kept φ T e Y) (hc:c<b)(hh:c≤e)(hu:0≤ c)
local notation "a'"=> (↑(sigma y):ℝ)
-- exact rates by perturbed family for any slack
include h hS hT hF hJ hb hp he hc hh hu hA hG hΓ
private lemma cash_rate {r u' v' ξ ρ : ℝ}{q k' : L→ℕ}
    (hk:Height C.S φ T n r)(hk':Height C.S φ T q u') (hY: Height C.S φ T l v') (hV: Height C.S φ T k' ξ)
    (hv:r < u')(hf:u'<b)(hw:u'<v')(hz:v'<ξ)(hi:c<r)(hy:e<v')(hR:0<ρ): RateLE φ T R (δ+(a'+ρ*Fintype.card J)*ξ):=by -- m here current matcher m → c'>b, cannot! name f
    obtain ⟨μ,hμ,ht⟩:= admitted U y hT hV hR
    apply (hA.mul (hμ.pays hT)).of_norm_le; filter_upwards [hall_range hT hk hY hk' hV hF hv hw hf hz 1 (Fintype.card J), ht, hG, hS, hΓ,hp.short hi hT (Moment_gap hT hk hi), he.short hy hT (Moment_gap hT hY hy), hk.earlier ((hv.trans hf).trans hb) hT hJ] with i hP ht hX hs hg hr hZ hw
    obtain ⟨f',Y,hV,hF,hY,hK,-⟩:= hs.wins
    exact viewing_admits U h hw.le hX hZ hr hg hP hF hY hK ht

lemma offered_cost : RateLE φ T R (δ+(a')*e) :=by
    intro r hr; obtain ⟨μ,hμ,hU,hδ⟩: ∃ u : ℝ, 0<u∧ u<b-c ∧ δ+(a'+u*Fintype.card J)*(e+u) < r:=by
       let x u:=δ+(a'+u*Fintype.card J)*(e+u); have hv: x 0 < r:= by simpa [x] using hr
       have ht : ∀ᶠ u:ℝ in 𝓝[>] 0, x u < r:=
          ((show Continuous x from by unfold x; fun_prop).continuousAt.tendsto.eventually (gt_mem_nhds hv)).filter_mono nhdsWithin_le_nhds
       have hf : ∀ᶠ u:ℝ in 𝓝[>] 0,u<b-c:= eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (sub_pos.mpr hc))
       exact ((show ∀ᶠ u:ℝ in 𝓝[>] 0,0<u from self_mem_nhdsWithin).and (hf.and ht)).exists
    have hP:= C.path.levels.fits.mesh; obtain ⟨n,h₁⟩:= found hT hP (show 0≤c+μ/4 by positivity); obtain ⟨l,h₂⟩:= found hT hP (show 0≤c+μ/2 by positivity); obtain ⟨k',h₃⟩:= found hT hP (show 0≤e+3*μ/4 by linarith only [hu,hh,hμ]); obtain ⟨l',h₄⟩:= found hT hP (show 0 ≤ e+μ by linarith); exact cash_rate (h:=h) U y hT hS hG hΓ hA hF hJ hb hp he hc hh hu h₁ h₂ h₃ h₄ (by linarith) (by linarith only [hU,hμ]) (by linarith) (by linarith) (by linarith) (by linarith) hμ r hδ

lemma see_cost (v:L→Viewers U) : RateLE φ T (fun i=> observe (spectator U (v i)) (beside (w i) (Y i)) (beside g y) - observe (spectator U (v i)) (beside (sole (0:E4)) (Y i)) (beside (D i) y)) (δ+(a')*e):=by
    apply (offered_cost (h:=h) U y hT hS hG hΓ hA hF hJ hb hp he hc hh hu).transfer
    filter_upwards [(Kept.sole φ T (fun _=> (0:E4)) e|>.chorus he (hp.mono hh)).inject,hΓ] with i hi hh; rw [← glance_sees U (v i) _ _ hi,← glance_sees U (v i) _ _ hh, ← map_sub]; exact glance_bound ..
end YM.OPE
