import YM.TraceExtension.Shelves.Mori
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Shelves
open Function Filter Lattice RG Wilson Labels Source Extra.Histories Bid MergeProof.Accent MergeProof
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open MeasureTheory
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay Pull Terrace Terrace.Glade Perfect Turret Margin Slate
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
local notation "Fᵣ"=> C.labels.level 4
local notation "Zᵣ"=> C.labels.level 5
variable {X:Axis→ Logs C 5}(hp:∀ i,TravelsC (𝓛:Filter (ℕ×ℕ)) (exhibit t i) (Readout t i) (X i).v (X i).x)
open StressFlux Next.UVStress Margin
variable (Hδ:Moonlit C.path r (PhysicalNext.Repeat.Legato.Bandage.renal C.path.levels) u D)(hr:∀ᶠ i in atTop,2 ≤ r i)(hA:auraQ C.path.levels TileNo)
variable {L:PaceBook C}(hL:Rod t none (𝓛:Filter (ℕ×ℕ)) L)
variable {S:Table C.book}{J:Scaling S}{H:(Cells.standard C).Hierarchy}{V:∀ i,Vane C i}{Y:∀ d i:ℕ,(Cells.standard C).Field d→L[ℂ] C.label d}(hq:Gondola F H J 𝓛 V Y)
variable (H':S.Hierarchy)(HF:F.PointLimits C S) (hq': StarPath F H J H' 𝓛)
variable {S₁:DiffPlan S}{P₁:DiffPlan (Cells.standard C)} (hJ:S₁.Derivatives S)(hP:P₁.Derivatives (Cells.standard C)) (ho:P₁.Orientation H.spin)
variable {s:ℕ→ Bowl (C.labels.level 5) →L[ℝ] (TableOne H.spin)} (hY:Spun Z J V H s)
open Asymptotics
local notation "F!"=> Cells.standard C
local notation "P!"=> Stern V
section portrait
lemma inter_turn (F':Frame G 4)(v:Axis→Axis→F'.Coeff)(a b:Axis): Plot (Prism F') (inter v) a b=inter (Plot (Prism F') v) a b:=by
    unfold inter; rw[plotEq,plotEq,plotEq,← Finset.sum_add_distrib, Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; rw [map_smul, map_add]; module
lemma inter_linkL{E V:Type*}[AddCommGroup E][Module ℝ E][AddCommGroup V][Module ℝ V](A':E→ₗ[ℝ] V)(v:Axis→Axis→ E)(i j:Axis): A' (inter v i j)=inter (fun i j=>A' (v i j)) i j:=by unfold inter; rw [map_smul,map_add]
lemma Courtis(H₁:(F!).Hierarchy)(w:Fin 3→ℝ)(i j) : Hill4 C (BillC Fᵣ w i j)= material (F!) (Fin.cons 0 w) i j:=by
    let v:=(F!).project 4 (BillC (Fᵣ) w i j); let J:=material (F!) (Fin.cons 0 w); have hx:v=J i j:=rfl; have hp: expectation _ 4 (J i j)=0:=by
        rw[expectation_is J i j]; unfold J; change oneStress (Bel C.book) (material (Bel C.book) (Fin.cons 0 w)) _ _ _=_; rw[oneStress_formula]; simp
    change centering (F!) 4 v= J i j; rw [hx,value_center,hp,zero_smul,sub_zero]
lemma MaterialSym(w:StressFlux.Coeff)(a b:Axis): inter (material (Cells.standard C) w) a b=material (Cells.standard C) w a b:=by
    let L:= material (Cells.standard C) w; have hP:L a b=L b a:=congr_arg (StressFlux.fromPol _ ) (stress_symm w a b (G:=G)); change inter L a b=_; unfold inter; rw [← hP]; change (1/2:ℝ) • (L a b+_)= L a b;module
end portrait
include P h hb hz ht hu hq H'
def materialB(C:Family G)(t:Bend):= material (Cells.standard C) (Fin.cons 0 (BornZ t))
def Zees(S:Table C.book)(f:S.Stress): S.Field 4:=∑ j:Axis,f j j
def Phase4 (X:Scaling S)(V:∀ i,Vane C i)(Z:Arch C)(k:ℕ): S.Stress→ₗ[ℝ] (Cells.standard C).Stress where
   toFun f i j:= Hero X V Z 4 k (f i j)
   map_add' x y:= funext fun i=>funext fun j=> (Hero X V Z 4 k).map_add ..
   map_smul' c x:= funext fun i=>funext fun j=> ((Hero X V Z 4 k).restrictScalars ℝ).map_smul c (x i j)
lemma chartB (k j:ℕ) (hj:P! j=k)(X:PaceBook C)(hp:C.ref 4 ≤ k): Phase4 J V Z j (baron S X k)=fun a b=> inter (fun i j' => Moment4 Z J V j (Shine4 Z X k i j')) a b :=by
    subst k; let k:=P! j; let c:= Moment4 Z J V j; funext i b; change Hero J V Z 4 j (baron S X k i b)=_; unfold baron; rw [heroicB P hb hz H' j _ hp];
    let Q:= OrbitT (Fᵣ) (StormP C X k); have ht' (i j'): swale Z 4 k (Q i j')=Shine4 Z X k i j':= strikes P ht hb hz _ hp _ i j'
    have he : press X k i b= inter Q i b:= inter_turn _ _ _ _; rw [he];
    let N:= (c.toLinearMap.restrictScalars ℝ).comp ((swale Z 4 k).restrictScalars ℝ)
    have hg : (fun i j'=>c (Shine4 Z X k i j'))=fun i j'=> N (Q i j'):=by funext i j'; rw[← ht'];rfl
    change N (_ )= inter _ i b; rw [inter_linkL,hg]
variable {B:Bend}{P':PaceBook C}(hτ:Rod t B (𝓛:Filter (ℕ×ℕ)) P') (hZ : Tendsto (Moment4 Z J V) atTop (𝓝 (Hill4 C)))
include hτ hZ
set_option maxRecDepth 4096 in
lemma nearing_h : Tendsto (fun k=> Phase4 J V Z k (baron S P' (P! k))) atTop (𝓝 (materialB C B)) :=by
    let X:= Phase4 J V Z; let v:= BornZ B; let Gm:=materialB C B; have hP :Tendsto (P!) atTop atTop:= (Sstar A).comp hq.growth
    let B'(k i j):= Moment4 Z J V k (Shine4 Z P' (P! k) i j)
    have he:Tendsto (Shine4 Z P') atTop (𝓝 (BillC (Fᵣ) v)):= continuous_fst.continuousAt.tendsto.comp (tiara P h hb hu hz hτ)
    have hx(a b:Axis): Tendsto (fun k=>B' k a b) atTop (𝓝 (Gm a b)):=by rw [show Gm a b=_ from (Courtis H v a b).symm]; exact Dash.arcing hZ ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp he a) b).comp hP)
    refine tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=> ?_; have hu:Tendsto (fun k=>inter (B' k) i j) atTop (𝓝 (inter Gm i j)):= ( (hx i j).add (hx j i)).const_smul (1/2:ℝ); rw[show inter Gm i j=Gm i j from MaterialSym ..] at hu; exact hu.congr' (((hP.eventually_ge_atTop (C.ref 4))).mono fun k hk=>by exact (congr_fun (congr_fun (chartB P h ht hb (t:=t) ‹_› hz hq H' _ k rfl P' hk) i) j).symm)
variable (hc: CellHyp C F)
include hc HF K θ hT hM in
lemma muteP (p:ℕ)(hl: B≠some true): Tendsto (fun i=> H! (P! i) ^ p • ∑ a:Axis, Phase4 J V Z i (baron S P' (P! i)) a a) atTop (𝓝 0):=by
   let F₁(j):= baron S P' j; let v(k):= Zees S (F₁ k); have hx:Fast C.S v:= Thin P h θ K ht hM hT hb H' hc HF hu B P' hτ hl
   have ht(k:ℕ):centering S 4 (v k)= v k:=by unfold v Zees; rw [map_sum]; refine Finset.sum_congr rfl fun i _=> ?_; change centering _ _ _=_; rw [value_center,(kernel_mem.mp (stitch_k H' P' k)).2]; simp
   refine (Vigor P h hb hz hq hx ht p hZ H').congr fun i=>?_ ; unfold v Zees; rw [map_sum];rfl
end YM.Trace.Shelves
