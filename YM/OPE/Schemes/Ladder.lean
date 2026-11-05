import YM.OPE.Schemes.Read
/-!
# Grid layer estimate

`for_plot` buys the replica radii for the *same* root mismatch across all
width-qualified exterior tests (including exactly these polarizers). The
geometry gap in the estimate below leaves room for a high horizon. For low
channels use the success of the spectral detectors; for high ones, prices at
every grade: a crude all-channel norm budget here might actually consume the
entire precision of the gauge estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Set Filter Table Lattice RG Wilson MergeProof Ribbons Accent PhysicalNext.Repeat.Legato Source Bid Next.Extract Next.UVStress
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S){I J L : Type}[Fintype I][DecidableEq I][Fintype J]{φ:Filter L}[φ.NeBot] {T A V : L→ℝ} {x v u a b c d e y z η : ℝ} {k m j: L→ℕ} (g:I→ C.book.Token) (r:J→ C.book.Token) {X:L→ I→ Cover}{Y:L→J→ E4} {q q':ℕ}
    {P:L→ C.label q}
variable {M} {E : Dash.Bin M} {t} {H} (Base' : Base C F M t E S H)
local notation "Λ" => U.sector.derivatives
variable {R: Prescription U.sector.derivatives}(hR:R.Coherent) (hT:Tendsto T φ atTop)
variable (hG:G.Simple) {W r' D}(L':Package C W r' D)(h:Org.Grill C F)

private lemma far (a b:ℝ)(u:ℕ)(ha:b<a) : ∀ᶠ v:ℕ in atTop, (u+1:ℝ)*a ≤ ((v:ℝ)+1/16)*(a-b):= ((tendsto_atTop_add_const_right _ (1/16) (tendsto_natCast_atTop_atTop (R:=ℝ))).atTop_mul_const (sub_pos.mpr ha)).eventually_ge_atTop _

set_option quotPrecheck false
def tax {I:Type}[Fintype I]{G:Gauge}{S:Register G}(x:I→ S.Token)(c d:ℝ) := (sigma x:ℝ)*d + 4*(Fintype.card I:ℝ)*(d-c)
local notation "w'" => (fun i=> C.S.gridPoint (j i) ∘ X i)
local notation "u'" => tax g a d
variable (i₀:I) (hk:Height C.S φ T k b)(hm:Height C.S φ T m a)(hj:Height C.S φ T j d)(hb: 0<b)(ha:b<a)(hu:a<x)(hd:x<d)
    (hx:extentWithin φ T (fun i=> C.S.gridPoint (j i) ∘ X i) x)(hy:Kept φ T x (fun i=> C.S.gridPoint (j i) ∘ X i))
    (he:∀ᶠ i in φ, Screen (C.S.gridPoint (j i) ∘ X i))
include U hk hm hj hb ha hu hd hx hy he i₀ hG L' Base' hR h hT
lemma grid_coeff (w : Mode Λ): RateLE φ T (fun i=> R.ope w (w' i) g 0) ((u')-w.1*a):=by
    have hϑ:= ha.trans (hu.trans hd); obtain ⟨q,hF,hq⟩ := ((far a b w.fst ha).and (eventually_ge_atTop w.fst)).exists
    obtain ⟨A,p,Q,h₁,h₂,hS⟩:= for_plot U g hT i₀ hG L' hk hm hj ha hu hd q hx hy
    have hf:= det_cost (R:=R) U g hT hS h w he hx hy (hb.trans (ha.trans hu)) hk hj hb hϑ h₂
    have hQ:= at_grade U g Base' hT hS L' hG hR w hm (h₁.pays hT) hq
    let f i:= R.ope w (w' i) g 0; let u i:=R.test w _ (S.project _ (Q i))
    apply RateLE.congr (RateLE.add (hf.mono ?_) (hQ.mono ?_) hT) (Eventually.of_forall fun i=> (sub_add_cancel (f i) (u i)))
    · unfold tax; unfold sigma; linarith only [hF,hb,ha]
    unfold tax; unfold sigma; rw [Nat.cast_sub hq]; linarith only
variable (s:L→ Viewers U)
local notation "T'"=> (fun i=> observe (spectator U (s i)) (beside (w' i) (Y i)) (beside g r))
local notation "Q'"=> (fun z i=> observe (spectator U (s i)) (beside (sole 0) (Y i)) (beside (sole (R.letter z)) r))
local notation "cost'"=> ((sigma r:ℝ)*u)
omit U hk hm hj hb ha hu hd hx hy he i₀ hG L' Base' hR -- replace
variable (hV: Intervals φ T c (centerless L) Y)(hp:Kept φ T u Y)(ht: 0≤c)(hl:c ≤ u)
include hV hp ht hl U h hT
lemma cloudRead {R:Prescription U.sector.derivatives} (w:Mode U.sector.derivatives): RateLE φ T (fun i=> observe (spectator U (s i)) (beside (sole 0) (Y i)) (beside (sole (R.letter w)) r)) (w.fst*c+(cost')):=by
    apply (viewer_cost U h (sole (R.letter w)) r hT s (Kept.sole φ T (fun _=>0) _) hp hV ht hl).mono; simp only [sigma, Fintype.sum_unique]; rfl
include U hk hm hj hb ha hu hd hx hy he i₀ hG L' Base' hR
lemma grid_remainder (hc:c<b) (N:ℕ): RateLE φ T (fun i=> (T' i) - R.truncated (spectator U (s i)) N (w' i) g 0 (Y i) r) ((u')-(N+1:ℝ)*(a-c)+(cost')) :=by
    let x':= u'-(N+1:ℝ)*(a-c); let t':= x'+cost'; let z:=(centerless (U:=E4) L)
    obtain ⟨q,hF,hq⟩:= ((far a b N ha).and (eventually_ge_atTop N)).exists
    obtain ⟨A,p,Q,h₁,h₂,hS⟩:= for_plot U g hT i₀ hG L' hk hm hj ha hu hd q hx hy; let v (w) i:= R.test w _ (S.project q (Q i)); let f (w) i:= R.ope w (w' i) g 0
    have he1:= director_space hT hx hV (hc.trans (ha.trans hu)); have hxy := (hy.mono (le_max_left x u)|>.chorus (hp.mono (le_max_right ..)) (he1.mono ((hc.trans (ha.trans hu)).le.trans (le_max_left ..)))|>.inject)
    let W(i):= spectator U (s i); let P' i:= observe (W i) (beside (z i) (Y i)) (beside (sole (⟨q,Q i⟩:C.book.Token)) r)
    have hs:RateLE φ T (fun i=>T' i-P' i) t' := (see_cost (h:=h) U r hT hS he hxy h₂ hk hj (ha.trans (hu.trans hd)) hV hp hc hl ht s).mono (by unfold t' x' tax; linarith only [hF, mul_nonneg (a:=(N+1:ℝ)) (by positivity) ht])
    have ha':∀ w: Mode Λ,w∈ bands Λ q → RateLE φ T (v w) ((u')-w.fst*a):=fun w hw=>(at_grade U g Base' hT hS L' hG hR w hm (h₁.pays hT) ((full_bands ..).1 hw)).mono (by unfold tax; rw [Nat.cast_sub ((full_bands ..).1 hw)]; linarith)
    have hu(w:Mode Λ)(hw:w∈ bands Λ N):RateLE φ T (fun i=>(v w i-f w i)*Q' w i) t':=by
       have ht':(w.fst:ℝ) ≤ N:= by exact_mod_cast ((full_bands ..).1 hw)
       let V:=u'-(q+1/16:ℝ)*(a-b); have hv: RateLE φ T (fun i=> f w i-v w i) V:= det_cost U g hT hS h w he hx hy (hb.trans (ha.trans hu)) hk hj hb (ha.trans (hu.trans hd)) h₂
       have hv: RateLE φ T (fun i=> v w i-f w i) V:=hv.neg.congr (Eventually.of_forall fun i=> (neg_sub _ _)); have hc:= (hv.mul (cloudRead (R:=R) U r hT h s hV hp ht hl w)).mono (b:=t'); apply hc; unfold t' V x'; linarith only [hF,mul_le_mul_of_nonneg_right ht' ht,ht]
    have hr(w: Mode Λ)(hw:w ∈ bands Λ q \ bands Λ N): RateLE φ T (fun i=>v w i*Q' w i) t':=by
       have hm:= w.fst; have hh: (N:ℕ)< w.fst:= lt_of_not_ge (fun h=>(Finset.mem_sdiff.mp hw).2 ((full_bands ..).mpr h))
       refine ((ha' w (Finset.mem_sdiff.mp hw).1).mul (cloudRead (R:=R) U r hT h s hV hp ht hl w)).mono ?_; have hx': (↑(N+1:ℕ):ℝ) ≤ w.fst:= by exact_mod_cast hh
       unfold t' x'; push_cast at hx'; linarith only [mul_le_mul_of_nonneg_right hx' (sub_nonneg.mpr (hc.le.trans ha.le))]
    have hL: RateLE φ T (fun i=> P' i- R.truncated (W i) N (w' i) g 0 (Y i) r) t':=by
       apply RateLE.congr ((RateLE.sum hT hr).add (RateLE.sum hT hu) hT); filter_upwards [Intervals.inject hV hp] with i hi
       rw [show P' i= _ from (R.sumAll (W i) r (spectate_ready U (s i)) (spectate U (s i)).laws.toSymmetric (spectate_respects U (s i)) hi (hR) (Q i)).symm]; unfold Prescription.truncated Prescription.termRead
       change _+_ = (∑ w∈ bands Λ _, v w i * Q' w i)-(∑ w∈ bands Λ _,f w i * Q' w i); rw [← Finset.sum_sdiff (f:=fun w=> v w i*Q' w i) (show bands Λ N⊆ bands Λ q from fun x hx=> (full_bands ..).2 (((full_bands ..).1 hx).trans hq)), add_sub_assoc]; congr 1; simp_rw [sub_mul,Finset.sum_sub_distrib] -- name?
    exact (hs.add hL hT).congr (Eventually.of_forall fun i=> (sub_add_sub_cancel _ _ _))
end YM.OPE
