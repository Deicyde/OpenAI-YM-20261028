import YM.Extension.UV.Canon.State
import YM.Extension.UV.Initial
/-! This is an adapter for the common construction (no UV claim from Final itself). -/
set_option autoImplicit false
noncomputable section
open scoped Topology BigOperators
namespace YM.Extension.UV
open Set Function Startup PhysicalNext.Repeat.Legato Lattice RG Wilson
variable {G:Gauge}

abbrev NearbyAssignments (X:UVBuild G): Prop := ∃ f:ℝ→ℕ→∀ p, RG.Shoot.Trail X.tower.a p, f X.tower.a.clock.bar=X.engine.history ∧ ∀ b,NearTarget X.tower.a b → GoodRace X b (f b)
lemma startup_actual {X:UVBuild G} (h:AttachedStart X) (g:G.Simple) N p : ∃ e : Envelope X.tower.kin N p,
    DifferentiableOn ℂ (datum e) (inside X.tower.a N) ∧ (∀ z∈inside X.tower.a N, ‖datum e z‖≤1/4) ∧
    ∀ t f, |t-X.tower.a.clock.bar|≤X.tower.a.clock.bar/8 → GoodRace X t f → let u:= (f N p N).beta;
      u∈strictBand X.tower.a N ∧ (fun i U => (((f N p N).activities.E i U:ℝ):ℂ))=regular (datum e (u:ℂ)) ∧
        (fun i U => (((f N p N).activities.K i U:ℝ):ℂ))=hard e (datum e (u:ℂ)) := by
  obtain ⟨e⟩:= envelope_exists X.tower.kin N p h.1.top (h.1.startup _)
  refine ⟨e,datum_analytic e (h.1.startup _),fun _ hu=>datum_bound e (h.1.startup _) hu,fun t f ht hg=>?_⟩
  dsimp only; let u:=(f N p N).beta
  have hu : u∈strictBand X.tower.a N:= hg.domainMargin g ht N p N le_rfl (x:=u) (by rw [sub_self,abs_zero]; exact (div_pos (contour_bound X.tower.a N).1 (by norm_num)).le)
  have hz : (u:ℂ)∈inside X.tower.a N:= inside_ofPad N hu (Metric.mem_ball_self (div_pos (zero_lt_one.trans (X.tower.a.fits.delayed _)) (by norm_num)))
  have ha:= hg.canonical N p
  refine ⟨hu,funext (fun i => funext (fun U=> ?_)), funext (fun i => funext (fun U=> ?_))⟩
  · rw [regular_eq e, E_function_real X.tower.kin]
    exact congr_arg (fun x:Rep G _=> ((x.activities.E i U:ℝ):ℂ)) ha
  rw [force_eq e (h.1.startup _) hz, K_function_real X.tower.kin]
  exact congr_arg (fun x:Rep G _=> ((x.activities.K i U:ℝ):ℂ)) ha

lemma canonical_and_final (g:G.Simple) (b:ℝ) (hb:0<b) : ∃ X:UVBuild G, X.tower.a.clock.kernel.penalty=b ∧ Partial X ∧
        AttachedStart X ∧ NearbyAssignments X ∧
        ∀ N p, ∃ e : Envelope X.tower.kin N p, DifferentiableOn ℂ (datum e) (inside X.tower.a N) ∧ (∀ z∈inside X.tower.a N, ‖datum e z‖≤1/4) ∧
          ∀ t f, |t-X.tower.a.clock.bar|≤X.tower.a.clock.bar/8 → GoodRace X t f → let u:= (f N p N).beta;
          u∈strictBand X.tower.a N ∧ (fun i U => (((f N p N).activities.E i U:ℝ):ℂ))=regular (datum e (u:ℂ)) ∧
            (fun i U => (((f N p N).activities.K i U:ℝ):ℂ))=hard e (datum e (u:ℂ)) := by
  obtain ⟨X,hk,hX,hy,hs,hu⟩:= uv_canonical_delivery g hb
  refine ⟨X,hk,?_,hu,chooseGoodRaces hX hu g, startup_actual hu g⟩
  rw [← hk] at hy
  exact ⟨hX,hs,X.final_at g hX,Linear.nativeK _ X.tower.plan hy,Linear.K_tendsto _ X.tower.plan hy,X.current.1,X.histories g,Bare.physical X.C⟩
end YM.Extension.UV
