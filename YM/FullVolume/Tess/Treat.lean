import YM.FullVolume.Tess.Circle
/- weighted integration. This gives exactly complex ratio, with analytic derivatives by Beam.tendencies. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Tess
open Filter Function Set Metric MeasureTheory Lattice RG Ray Asymptotics
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
open Extraction Extraction.Lease Difference Amp Amp.Beam
variable {S:Schedule} {n N j m p:ℕ}{K K': Set (Points n)}
local notation "A"=>S.a
local notation "B"=> Beam ℂ
namespace Scroll
abbrev treats (S:Schedule) (U:ℕ→Positions n→Beam ℂ)(N p:ℕ) (t:Test n): Beam ℂ:= (S.a N:ℝ)^(4*n) • ∑ i:Var S n N p, t (tag (S.a N) (Lattice.lift ∘ i)) • U N (Lattice.lift ∘ i)
-- CLM complex
lemma pilotS (U:ℕ→Positions n→Beam ℂ)(N p:ℕ)(t:Test n){z:ℂ}(h:z∈optics): heartX (treats S U N p t) z= sumOn (fun i y=> heartX (U i y) z) S p N t:=by
   simp_rw [← halos _ h]; unfold treats sumOn
   have hv (i: Beam ℂ)(c:ℝ): haloC h (c • i)=c • haloC h i:=(haloC h|>.restrictScalars ℝ|>.map_smul c i)
   rw [hv,map_sum]
   simp_rw [map_smul]; rw [Complex.real_smul, Complex.ofReal_pow]; rfl
-- readability at real scalars includes tips ±1. direct using ∑ powers.Real linear into ℂ, need commut.
lemma viewport (U:ℕ→Positions n→Beam ℂ)(N p:ℕ)(t:Test n)(s:sun): read ℂ s (treats S U N p t)= sumOn (fun i y=> read ℂ s (U i y)) S p N t:=by
    have h(x:Beam ℂ)(c:ℂ):read ℂ s (c • x)=c • read ℂ s x:=by
         change ∑' i:ℕ,s.val^i • ((c • x) i) = c • ∑' i:ℕ,s.val^i • x i
         simp_rw [lp.coeFn_smul,Pi.smul_apply,smul_comm (s.val^_) c]; exact ((x.spar (abs_le.mpr s.property)).const_smul c).tsum_eq
    unfold treats sumOn; rw [map_smul,map_sum]; simp_rw [h]; rw [Complex.real_smul,Complex.ofReal_pow]; rfl
section
open Classical
variable (U:ℕ→Positions n→Beam ℂ) (t:Test n)
def edify (S:Schedule) (U:ℕ→Positions n→Beam ℂ) (p N:ℕ) (t:Test n)(x:Points n): B:= (Fund S p n).indicator (fun x=> t (tag (S.a N) (address (S.a N) x)) • U N (address (S.a N) x)) x
lemma stipend : Integrable (edify S U p N t) ∧ (∫ x, edify S U p N t x)= treats S U N p t:=by
    classical
    let V:=Var S n N p; let f (y:Positions n):= t (tag (A N) y) • U N y; let g(r:V):=f (Lattice.lift ∘ r); let X(r:V):= segment (S.a N) (Lattice.lift ∘ r); let T (r:V): Points n→Beam ℂ:= (X r).indicator (fun _=>g r)
    have hm(r):MeasurableSet (X r):= measurable_segment (S.a_pos _) _
    have ht(r):Integrable (T r):= (integrable_indicator_iff (hm r)).mpr (integrableOn_const (by rw [show volume (X r)=_ from cell_volume (S.a_pos _) _]; exact ENNReal.ofReal_ne_top)) -- remove
    rw [show edify S U p N t=∑ r:V,T r from ?_]; constructor
    · exact integrable_finsetSum' _ fun i _=>ht i
    · simp_rw [Finset.sum_apply]; rw [integral_finsetSum _ fun i _=>ht i,treats,Finset.smul_sum]; refine Finset.sum_congr rfl (fun j _=>?_); unfold T; rw [integral_indicator (hm j), setIntegral_const, measureReal_def, show volume (X j)=_ from cell_volume (S.a_pos _) _, ENNReal.toReal_ofReal (pow_nonneg (S.a_pos _|>.le) _)]
    funext x; rw [Finset.sum_apply]; unfold edify; by_cases hx:x∈ Fund S p n
    · let r:V:=bucket N p x; rw [indicator_of_mem hx,Finset.sum_eq_single r]; unfold T; rw [indicator_of_mem (show x∈ X r from found hx), show address (S.a N) x=Lattice.lift ∘ r from found hx]
      · intro i _ hi; exact indicator_of_notMem (fun h=> hi ((corners hx).unique h (found hx))) _ -- elaboration.L
      simp
    rw [indicator_of_notMem hx]; exact (Finset.sum_eq_zero (fun i _=> indicator_of_notMem (fun h=>hx (tile_in i h)) _)).symm
end
variable {U:ℕ→ Positions n→ Beam ℂ}{G:Points n→ Beam ℂ}(hk: Scroll S K U G)(t:Test n)
abbrev olive (t:Test n)(G:Points n→Beam ℂ):Points n→Beam ℂ:= fun x=> t x • G x
include hk
lemma elected (h:IsCompact K)(hh:tsupport t ⊆ interior K)(hp:suitable S p t) : Integrable (olive t G) ∧ Tendsto (fun i=> treats S U i p t) atTop (𝓝 (∫ x,olive t G x)):=by
    classical
    obtain ⟨c,hc⟩:= h.bddAbove_image hk.land.norm; let f i:= edify S U p i t
    obtain ⟨R,hR,H⟩:= Order.testSup t; let Z:=(Fund S p n).indicator (fun _=> R*(1+ max 0 c)); have he : Integrable Z:= (integrable_indicator_iff (full_box ..).1).mpr (integrableOn_const (full_box ..).2.ne)
    have hi :∀ᶠ i in atTop,∀ x, ‖f i x‖ ≤ Z x:=by
       filter_upwards [hk.wins 1 zero_lt_one] with i hi x; by_cases hx:x∈Fund S p n
       · unfold f edify Z; rw [indicator_of_mem hx, indicator_of_mem hx]
         let y:= address (S.a i) x; let q:=tag (A i) y; change ‖t q • U i y‖ ≤ _
         rcases eq_or_ne (t q) 0 with hy|hy; rw [hy, zero_smul, norm_zero]; positivity
         have hp : q∈K:= interior_subset (hh (subset_closure hy)); rw [norm_smul]; apply mul_le_mul (H _) _ (norm_nonneg _) hR
         exact (norm_le_norm_sub_add (U i y) (G q)).trans (add_le_add ((dist_eq_norm _ _).symm.trans_le (hi _ hp|>.le)) ((hc ⟨_, hp,rfl⟩).trans (le_max_right ..)))
       unfold f edify Z; rw [indicator_of_notMem hx,indicator_of_notMem hx,norm_zero]
    have hU(i):AEStronglyMeasurable (f i) volume:= (stipend U t).1.aestronglyMeasurable
    have hv(x): Tendsto (fun i=> f i x) atTop (𝓝 (olive t G x)):=by
        by_cases hx:x∈ Fund S p n
        · unfold f edify; simp_rw [indicator_of_mem hx]; rcases Classical.em (x∈tsupport t) with hi|hi; have ht := Extraction.chosen x (S:=S); exact (t.continuous.continuousAt.tendsto.comp ht).smul (hk.inure tendsto_id (hh hi) ht)
          have he :∀ᶠ i in atTop,tag (A i) (address (A i) x) ∉ tsupport t:= (Extraction.chosen x (S:=S)).eventually ((isClosed_tsupport _).isOpen_compl.mem_nhds hi)
          unfold olive; rw [show t x=0 from (by by_contra h; exact hi (subset_closure h)),zero_smul]; apply tendsto_const_nhds.congr' -- stuck
          filter_upwards [he] with i hi; rw [show t _=0 from (by by_contra h; exact hi (subset_closure h)), zero_smul]
        have ht:t x=0:=by
           by_contra h; have hv:=hp (subset_closure h); exact hx (show ∀ i v, _ < x i v ∧ x i v ≤ _ from fun i v=> ⟨(hv i v).1,(hv i v).2.le⟩)
        unfold f edify olive; simp_rw [ht,zero_smul,indicator_of_notMem hx]; exact tendsto_const_nhds
    refine ⟨he.mono' (aestronglyMeasurable_of_tendsto_ae atTop hU (Eventually.of_forall hv)) (Eventually.of_forall fun x=> le_of_tendsto (hv x|>.norm) (hi.mono fun i hv=> hv x)), (tendsto_integral_filter_of_dominated_convergence Z (Eventually.of_forall hU) (hi.mono fun i H=> Eventually.of_forall H) he (Eventually.of_forall hv)).congr' (Eventually.of_forall fun i=> (stipend U t).2)⟩
end Scroll
end YM.FullVolume.Tess
#print axioms YM.FullVolume.Tess.Scroll.pilotS
#print axioms YM.FullVolume.Tess.Scroll.viewport
#print axioms YM.FullVolume.Tess.Scroll.elected
