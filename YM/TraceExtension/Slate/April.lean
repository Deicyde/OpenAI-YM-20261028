import YM.TraceExtension.Slate.Club
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Slate
open Function Filter Lattice RG Wilson Labels Source Extra.Histories Bid MergeProof.Accent MergeProof
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open MeasureTheory
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay Pull Terrace Terrace.Glade Perfect Turret Margin
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
variable (P:C.Makes) (h:G.Simple) (θ:PostT C.path.levels)(K:Stock.Tabs C.path.levels)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (ht:Scrim C W u ψ φ δ (fly C.path.levels) r D)(hM:Sceptre C W) (hT:supportQ C.path.levels)
variable {F:Extraction.Order}{𝓛:Ultrafilter (ℕ×ℕ)} (hb:(𝓛:Filter (ℕ×ℕ))≤F.fuse)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "V!"=> C.path
local notation "b!"=> (𝓛:Filter (ℕ×ℕ))
local notation "H!"=> C.path.levels.clock.hatBeta
variable {t:Tickets C} (hu:Grant C (𝓛:Filter (ℕ×ℕ)) t)
open Zn
variable {d:ℕ}{Z:Arch C}(hz:steep 𝓛 Z)
open Finset StressFlux
-- uniform asymptotics iff given paths of schedules.Any thresholds.Walt exact and quantitative.
abbrev tribe : Fin 3→ℝ:= (![1,-1/4,1]:Fin 3→ℝ)
abbrev BornZ(i:Bend):Fin 3→ℝ:= i.elim (-tribe) azure
abbrev LangC(F:Frame G 4)(t:Fin 3→ℝ)(x y:Axis):= F.coords (stress G (Fin.cons 0 t) x y)
abbrev Vivid (F:Frame G 5) (t:Fin 3→ℝ):= (plate F).symm (bareVector t)
def BillC(F:Frame G 4) : (Fin 3→ℝ)→ₗ[ℝ] Axis → Axis → F.Coeff where
    toFun := LangC F
    map_add' x y:=by
       ext1 i;ext1 j; have hu : Fin.cons (α:=fun _ : Fin 4=>ℝ) 0 (x+y)= Fin.cons 0 x+Fin.cons 0 y:=by ext1 i; cases i using Fin.cases <;> simp
       unfold LangC; rw[hu,map_add]; exact F.coords.map_add ..
    map_smul' t x:=by
       ext1 i;ext1 j; have hu : Fin.cons (α:=fun _ : Fin 4=>ℝ) 0 (t • x)= t • Fin.cons 0 x:=by ext1 i; cases i using Fin.cases <;> simp
       unfold LangC; rw[hu,map_smul]; exact (F.coords.toLinearMap.restrictScalars ℝ).map_smul ..
lemma Jure(F:Frame G 4)(H:G.Simple): Injective (BillC F):=by
   intro x y he; let x':=Fin.cons (α:=fun _=>ℝ) 0 x; let y':=Fin.cons (α:=fun _=>ℝ) 0 y
   have hz:x'=y':=stress_detect H (show labelStress x'=labelStress y' from Subtype.ext (funext fun i=>funext fun j=> F.coords.injective (congr_fun (congr_fun he i) j)))
   exact funext fun i=> by simpa [x',y'] using congr_fun hz i.succ
lemma bust (F':Frame G 5): Vivid F' tribe = Stem5 F':=by change (plate F').symm (bareVector _)=_; unfold Stem5; apply congr_arg; exact Subtype.ext eom_vector_raw
lemma Vivid_z (F':Frame G 5): Vivid F' (-tribe)= -Stem5 F':=by rw [← bust]; unfold Vivid; rw[map_neg,map_neg]
lemma bPay (T:Labels.Frame G 4)(i j:Axis): BillC T (-tribe) i j=T.coords (-raw G i j):=by rw[map_neg (BillC T)]; change _=_;rw[map_neg];rfl
lemma Crown0(F:Frame G 4)(t:Fin 3→ℝ):OrbitT F (BillC F t)=BillC F t:= lamp _
section limits
variable {H:Hol G}{F':Labels.Frame G 4}{Z:Labels.Frame G 5}
variable {U:Type}{L: Filter U}{x:U→ℝ}{g:U→ Side}{Y:∀ i,Dart G (g i)}{R:∀ i,Rep G (g i)}{w:U→ Fin 3→ℝ} (hx:Tendsto x L atTop)(hg:Tendsto (fun v=>(g v).val) L atTop)(h:G.Simple)
variable (hp:∀ i,Nonwrapping (Wicket.tempQ (x i) (n:=g i)) 0)(hy:∀ i,Sight (x i) (R i) (Y i))(hs:∀ i,Club (R i) (x i) (Meld (Y i) (x i))) (hv:∀ i,4 ≤ (R i).p.order)(hw:∀ i,Walt F' Z H (x i) (Meld (Y i) (x i)) (w i))
include hp hx hg h hy hs hv hw
lemma autumn : Tendsto w L (𝓝 (-tribe)) :=by
    have hu:Tendsto (BillC F' ∘ w) L (𝓝 (BillC F' (-tribe))):=by
        have hm:Tendsto (fun i=> cardX F' H (x i) (Meld (Y i) (x i))) L (𝓝 (BillC F' (-tribe))):=by
             refine tendsto_pi_nhds.mpr (fun j=>tendsto_pi_nhds.mpr (fun k=>?_)); rw [bPay]; exact arch_p hg hx hp h hs hy hv ..
        rw [← Crown0]; exact (((OrbitT F').continuous.tendsto _).comp hm).congr (fun i=>funext fun j=>funext fun k=> (hw i).truth j k)
    obtain ⟨u,hU⟩:= (BillC F').exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (Jure F' h)); have he(i):u (BillC F' i)=i:= LinearMap.congr_fun hU i
    have hT:= u.continuous_of_finiteDimensional.continuousAt.tendsto.comp hu
    simp only [comp_def,he] at hT; exact hT
end limits
section slate
open Wicket
lemma reachBW {S:Stage}{x:ℝ}{n:Side} {Q:Labels.Frames G}{q:Quilt (Q.level 5) n}{H:Hol G}{T:∀ d,SectionData (Q.level d)}{L₁:ℝ}{R:Rep G n}(H':WorthB Q T H S x L₁ R q): Nonwrapping (tempQ x (n:=n)) 0:=by
   have hu:= H'.site; intro i hi; obtain ⟨j,hj,hj'⟩:=halo_spec.mp hi; rw[Finset.mem_singleton.mp hj,separation_comm] at hj';change separation i 0≤ high x+1 at hj';omega
-- all stages bounded comparison failure. No pre-L extra prices needed.
lemma pages(F':Frame G 4)(Z:Frame G 5)(H:Hol G)(h:G.Simple)(ε:ℝ)(he:0<ε) : ∀ᶠ x:ℝ in atTop,∀ (n:Side)(t:ℝ)(J:Dart G n)(R:Rep G n)(w:Fin 3→ℝ), Club R x (Meld J x)→ Sight x R J→ 20*(high x+10)< n.val→ Nonwrapping (tempQ x (n:=n)) 0 →Walt F' Z H x (Meld J x) w→ ‖w+tribe‖<ε:=by
    by_contra hp; rw[eventually_atTop] at hp; push Not at hp
    choose v hv n d J R w hR hJ hK hT hW hE using fun i:ℕ=> hp (i:ℝ)
    have hv':Tendsto v atTop atTop:= tendsto_atTop_mono hv tendsto_natCast_atTop_atTop
    have hx:Tendsto (fun i=>(n i).val) atTop atTop:=by refine tendsto_atTop_mono (f:=fun i=>Pressure.radiusB (v i)) ?_ (Work.E01.radiusB_tendsto.comp hv'); intro i; have hk:=hK i; unfold high at hk; omega
    obtain ⟨i,hi⟩:= (Metric.tendsto_nhds.mp (autumn h hv' hx hT hJ hR (fun i=> le_trans (show 4≤(6:ℕ) by norm_num) (R i).p.order_ge) hW) ε he).exists
    rw [dist_eq_norm,sub_neg_eq_add] at hi; exact (not_lt_of_ge (hE i)) hi
end slate
end YM.Trace.Slate
