import YM.AnalyticNext.GRID_STOP_ATTENUATION.Coarrival.Oper
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Harvest.Eco
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Circlet.Knoll
/-!
 # Cliff toll.Price S prereqs. c chosen at THIS layer before doors.Authors. no circular. Lens coupled to Frame forecasts motors of B.Stamps.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Circlet
open Function Filter Set Lattice Wilson Source RG RG.Supply Pressure Tree Next.SectorChange Finset
open Push Push.PriceCompiler Push.AbsoluteSums Gas JointLoad JointLoad.Heir JointLoad.Heir.Suite Input Org Labels
open Extra.Histories Extra.Histories.Doors Next.Foundations
open AnalyticBridge.VerifiedReset.Time Next.Scheduling Next.Fluctuations ThroughLaunch
open Planned.PrimaryIntegral295 PPX Planned.GuardedAtom
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{j t d:ℕ}
variable (G)

def credibility (e₀ : ℝ)(i q:ℕ):ℝ:= Real.exp e₀ * Next.Foundations.price G (max i q)
-- coverNumber ≤1, no clip dependency. raw→tab δ shape.Unwrap.L scaling

def usage (n p d:ℕ)(u : ℝ) := Push.Local.factor (hol G) (localSection G d) u (Next.Foundations.price G (max n p))
def billG (i p n q d:ℕ)(s t : ℝ)(Z : ℝ):ℝ:= credibility G t n q * (1 + usage G i p d s * (1+2*(Z+1))*(Push.Local.turnCost i p+1))
variable {G}

-- Startup alignment at IMPORT Orders heights are the only fees.We Can pick per-frame.D before s. One leading triangle C Forecast.Re uses Work clock t.Update.
variable {O:ThroughLaunch.Orders}(r:ℕ→ℕ→ℕ) (K:KernelChoices) (hp:Draft O)
-- Driven AFTER pledge transport by stage.Equalities.
set_option quotPrecheck false
local notation "F"=> ((Labels.frames G).level d)
local notation "T"=> localSection G d
abbrev Charge (s:Sheet G)(d j i :ℕ)(x:((frames G).level d).Index)(r:ℕ) := Cliff G (s.profile i).order (s.profile i).power (s.profile j).power ((((frames G).level d).grades x).1-1) j i r (s.profile i).supportExponent (s.profile j).supportExponent s.kernel

def Chop (s:Sheet G)(C:ℕ→ℝ)(r:ℕ→ℕ→ℕ):Prop := ∀ j i,StepStages j i→ s.first≤ i→∀ d,d+3≤ i→
    (∀ (x:((frames G).level d).Index), x≠0 → ∃ V: Charge s d j i x (r j i), billG G (s.profile i).order (s.profile i).power (s.profile j).order (s.profile j).power d (s.profile i).supportExponent (s.profile j).supportExponent V.charge ≤ C j)∧
    ∀ (hj : 4≤j) (hi:4≤ i) (hd:d≤j), Seal.limit (localSection G d) (sound G d) s.kernel.penalty_pos hi (Next.Foundations.valuation G d) hj hd (one_le_two (α:=ℝ)) ≤ C j -- ratio2

include hp
lemma ransom (j i d:ℕ)(h:StepStages j i)(hi:O.first≤ i)(hz:d+3 ≤ i)(x: ((frames G).level d).Index):∃ z:ℝ,1≤z∧∀ s:Sheet G,s.kernel=K→WithStage s O→∃ V: Charge s d j i x (r j i),
    billG G (s.profile i).order (s.profile i).power (s.profile j).order (s.profile j).power d (s.profile i).supportExponent (s.profile j).supportExponent V.charge ≤ z := by
   have hj:d≤ j:=by have ht:=h.1; omega
   have hs : (((Labels.frames G).level d).grades x).1-1+2 ≤ j:= by have hx:=((Labels.frames G).level d).bound x; have ht:=h.1; omega
   have hy:= palladium G (O.jets i) (O.position i) (O.position j) ((((Labels.frames G).level d).grades x).1-1) j i (r j i) K (hp.positive i).le (hp.positive j) ((Nat.le_trans (Nat.sub_le ..) (((Labels.frames G).level d).bound x)).trans (hj.trans ((le_max_right ..).trans (hp.heights _)))) (hp.cut.trans (hi.trans h.1)) (hp.cut.trans hi) hs
   obtain ⟨V⟩:=hy
   let z:=billG G (O.jets i) (O.position i) (O.jets j) (O.position j) d (O.supportExp i) (O.supportExp j) V.charge
   refine ⟨max 1 z,le_max_left ..,fun s hK ht=>?_⟩; unfold Charge; rw [ht.jets,ht.powers,ht.powers,ht.prices,ht.prices,ht.jets,hK]; exact ⟨V,le_max_right ..⟩

-- C table. no assumption G dimensions re.SM.
lemma loch (G:Gauge) : ∃ C:ℕ→ℝ,(∀ j, 1 ≤ C j) ∧ ∀ s:Sheet G,s.kernel=K→WithStage s O→ Chop s C r:=by
   let g(j:ℕ):=(range (j+1)).product (range (j+1)) -- row finite
   have H(j:ℕ)(p:ℕ×ℕ) : ∃ z:ℝ,1 ≤ z∧ (∀ s:Sheet G, s.kernel=K→WithStage s O→ StepStages j p.1 → s.first ≤ p.1 → p.2+3 ≤ p.1 →
     (∀ (x:((frames G).level p.2).Index), x≠0 → ∃ V: Charge s p.2 j p.1 x (r j p.1), billG G (s.profile p.1).order (s.profile p.1).power (s.profile j).order (s.profile j).power p.2 (s.profile p.1).supportExponent (s.profile j).supportExponent V.charge ≤ z)∧
     ∀ (hj : 4≤j) (hi:4≤p.1) (hd:p.2≤j), Seal.limit (localSection G p.2) (sound G p.2) s.kernel.penalty_pos hi (Next.Foundations.valuation G p.2) hj hd (one_le_two (α:=ℝ)) ≤ z):=by
       obtain ⟨i,d⟩:=p; by_cases ht:StepStages j i∧O.first≤ i∧ d+3 ≤ i
       swap; exact ⟨1,le_rfl,fun _ h hp hu hz hi=>False.elim (ht ⟨hu,hp.first ▸ hz,hi⟩)⟩
       have hi:=hp.cut.trans ht.2.1; have hj:4≤j:=hi.trans ht.1.1; have hr:d≤ j:=by have := ht.2.2; have := ht.1.1; omega
       choose Z hZ H' using ransom (G:=G) r K hp j i d ht.1 ht.2.1 ht.2.2
       let Y:=1+∑ x,Z x; have hx:0≤∑ x,Z x:=Finset.sum_nonneg (fun x _=> zero_le_one.trans (hZ x))
       refine ⟨max Y (Seal.limit (localSection G d) (sound G d) K.penalty_pos hi (Next.Foundations.valuation G d) hj hr (one_le_two (α:=ℝ))), (le_add_of_nonneg_right hx).trans (le_max_left ..),fun s he hs _ _ _=>⟨fun x _ => ?_,fun _ _ _=>?_⟩⟩
       · obtain ⟨V,h⟩:= H' x s he hs; exact ⟨V,h.trans ((Finset.single_le_sum (s:=Finset.univ) (fun i _=> zero_le_one.trans (hZ i)) (Finset.mem_univ _)).trans ((le_add_of_nonneg_left zero_le_one).trans (le_max_left ..)))⟩
       subst K; exact le_max_right ..
   choose C hC hX using H
   refine ⟨fun j => 1+∑ p∈g j,C j p,fun j=> le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => zero_le_one.trans (hC ..))),fun s hh hp j i hi ht d hD=> ?_⟩
   obtain ⟨h1,h2⟩:= hX j (i,d) s hh hp hi ht hD; have hx : C j (i,d) ≤ 1+∑ p∈g j,C j p:= (Finset.single_le_sum (s:=g j) (fun x _=>zero_le_one.trans (hC j x)) (Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hi.1),Finset.mem_range.mpr (by have :=hi.1; simp; omega)⟩)).trans (le_add_of_nonneg_left zero_le_one)
   exact ⟨fun i he=>let ⟨v,h⟩:= h1 _ he; ⟨v,h.trans hx⟩,fun h p a=>(h2 h p a).trans hx⟩
end YM.PhysicalNext.Repeat.Circlet
