import YM.OPE.Schemes.Rearrange
/-!
# Portable estimates in a single positive layer
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Filter Set Lattice RG Wilson MergeProof Ribbons Accent Source PhysicalNext.Repeat.Legato Next.Extract Next.UVStress Bid Prescription
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S){I J L: Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{φ:Filter L}[φ.NeBot]{T:L→ℝ}{x a b c d t :ℝ}(g:I→ C.book.Token)(r:J→ C.book.Token){X:L→ I→ E4}{Y:L→J→ E4}{o:L→E4}
variable {M} {E : Dash.Bin M} {V} {H} (Base' : Base C F M V E S H)
local notation "Λ"=> U.sector.derivatives
variable (hT:Tendsto T φ atTop)(hG:G.Simple){W r' D}(L':Package C W r' D)(h:Org.Grill C F) {R: Prescription U.sector.derivatives}(hR:R.Coherent)

def enveloped (φ:Filter L)(T:L→ℝ)(a:ℝ)(X:L→I→ E4)(o:L→E4) := extentWithin φ T (fun i=>away (X i) (o i)) a

lemma Kept.away (h:Kept φ T a X)(s:L→ E4): Kept φ T a (fun i=>OPE.away (X i) (s i)):=by
    intro b hb; filter_upwards [h b hb] with i hi j k hj; unfold OPE.away; rw [sub_sub_sub_cancel_right]; exact hi j k hj
lemma Intervals.away (h:Intervals φ T a X Y)(s:L→E4):Intervals φ T a (fun i=> OPE.away (X i) (s i)) (fun i=> OPE.away (Y i) (s i)):=by
    intro b hb; filter_upwards [h b hb] with i hi j k; unfold OPE.away; rw [sub_sub_sub_cancel_right]; exact hi j k
lemma Rec_spacing (hT:Tendsto T φ atTop)(h:Intervals φ T a (fun i=> sole (o i)) Y)(he:enveloped φ T b X o)(hz:a<b): Intervals φ T a X Y:= shrinking hT hz he h
variable (hx:enveloped φ T a X o)(he:Kept φ T a X) (ha:0<a)
include h hT Base' L' hG hx he ha hR
lemma group_coeff (w:Mode Λ): RateLE φ T (fun i=> R.ope w (X i) g (o i)) (((sigma g:ℝ)-(w.fst:ℝ))*a):=by
    cases isEmpty_or_nonempty I with
    | inl hi=>
       simp only [empty_coeff R g _ _ U.room.kernel w]; by_cases h:w.fst=0; · simpa [sigma,h] using (RateLE.const (R.test w 0 (S.unit 0)) hT)
       rw [highVan U.room.kernel.laws.toSymmetric U.phase.transport.injection hR _ (Nat.pos_of_ne_zero h)]; exact RateLE.zero (X:=ℂ) _ _ _ -- name etc
    | inr hi=>
       obtain ⟨i⟩:=hi; apply RateLE.congr (common_rate U g Base' hR w hT (show Corridor φ T a (fun i=> away (X i) (o i)) from ⟨he.away o,hx⟩) ha h i hG L'); filter_upwards with i; exact (sub_self (o i):o i-o i=0) ▸ ope_away R g (X i) (o i) (o i) w
lemma group_remainder (s:L→ Viewers U) (hp:Intervals φ T b (fun i=> sole (o i)) Y) (hw:Kept φ T t Y)(ht:b≤t)(hh:b<a)(ho:0≤b) (q:ℕ): RateLE φ T (fun i=> observe (spectator U (s i)) (beside (X i) (Y i)) (beside g r) - R.truncated (spectator U (s i)) q (X i) g (o i) (Y i) r) ((sigma g:ℝ)*a-(q+1:ℝ)*(a-b)+(sigma r:ℝ)*t):=by
    have hV:= (((Kept.sole φ T o t).chorus hw (hp.mono ht)).inject)
    cases isEmpty_or_nonempty I with
    | inl hi=>
       apply RateLE.congr (RateLE.zero (X:=ℂ) _ _ _) -- inspect
       filter_upwards [hV] with i hi; rw [empty_test R _ _ _ _ _ _ _ U.room.kernel (spectate U (s i)) (spectate_respects U (s i)) (spectate_ready U (s i)) U.phase.transport.injection hR hi, sub_self]
    | inr hi=>
       obtain ⟨i⟩:=hi; have hξ:=(hw.away o); have hP: Intervals φ T b (centerless L) (fun i=>away (Y i) (o i)):= by have hf:=hp.away o; rw [show centerless (U:=E4) L= (fun i=> OPE.away (sole (o i)) (o i)) from funext fun i=> funext (fun _=> (sub_self (o i)).symm)]; exact hf
       let Y' i:= away (Y i) (o i); have hN:=Rec_spacing hT hp hx hh; have hg:= ((he.mono (le_max_left ..)).chorus (hw.mono (le_max_right ..)) (hN.mono (ht.trans (le_max_right ..))))|>.inject
       apply RateLE.congr (early_rate (Y:=Y') U g r Base' hR hT (show Corridor φ T a (fun i=> away (X i) (o i)) from ⟨he.away o,hx⟩) ha h i hG L' s hP hξ ho ht hh q); filter_upwards [hV,hg] with i hi hg; dsimp only [Y'];
       rw [ (beside_away (Y i) (X i) (o i)), observe_away _ _ _ _ ((spectate _ _).translations) hg, (show R.truncated (spectator U (s i)) q (away (X i) (o i)) g 0 (away (Y i) (o i)) r = _ from (sub_self (o i)) ▸ trunc_away R _ (Y i) _ _ _ _ (o i) (o i) (spectate _ _) hi)]
end YM.OPE
