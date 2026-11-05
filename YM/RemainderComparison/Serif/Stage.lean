import YM.RemainderComparison.Serif.Gallery

/-!
# Return also unmarked scalar circumference and REAL calibrations
Actual parameter model connection in subsequent modules.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Serif
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι α : Type}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic Muse Sleet
variable (Z:Set ι)(l:ι→ℝ) (δ:ℝ)
open Verse Marker Script
variable {β:Type} [DecidableEq β]{Jm:Census β}
variable (U:Pad H j χ)
local notation "F'"=> U.S.N
local notation "L₁"=> Muse.song M H χ U.V (∅:Set ℕ) 0
local notation "P₀"=> tax G L x
local notation "Lt"=> sits Z l δ
variable {τ κ K Y γ V T0:ℝ}
variable (h:Roles H χ U k s J I a d e K σ Y γ V T0) (hh:Motto M l δ H τ K Y I)
variable (z:ι→Poly Jm) {fP:β→ℝ} (hZ : Chorus Jm fP Z z k)
open Mallow Ovens Progress.DirectedRecipe
variable {R':Rep G f} (H':Cash W x μ L Q o C T R')(D:Match.Alliance H' H 1 0)(P':BudgetPoint) (E₀:ℕ→RegularAddress c)(V₀:ℕ → Config G c→ℝ)

local notation "VB" => Refrain.read H' D χ E₀ V₀
local notation "f'"=> Refrain.visa H' D
local notation "FR"=> foible M H χ Z l δ z H' D
local notation "BR"=> book M H χ Z l δ z H' D P' E₀ V₀
local notation "TR"=> tome M H χ Z l δ z H' D P' E₀ V₀
variable [Countable ι] (V:Config G c)
local notation "MX" p=> M ∘ Script.restrict p

-- input

def TuneR (S:StepData c f)(U:Config G f): Poly Jm:=∑' i:Drums M S,(raw M i).paint Z (sits Z l δ) z U

def Quota (S:StepData c f)(p:Finset ι): Config G f→Poly Jm:= let a:=Script.restrict p
                                                 TuneR (M∘a) (a ⁻¹' Z) (l∘a) δ (z∘a) S
local notation "TU" => TuneR M Z l δ z S
local notation "Qf"=> Quota M Z l δ z S
include h hh hZ
lemma chase : Tendsto (fun p=> S.push R.beta (Qf p) V) atTop (𝓝 (S.push R.beta TU V)):= by
   have hv:= Serif.input_pay M H χ Z l δ U h hh z hZ
   obtain ⟨t,hp,hF⟩:= hv
   let f i:= (raw M (i:Drums M S)).paint Z (sits Z l δ) z
   have hz : S.IsKernel R.beta G:= S.isKernel (funds_branch H.laws.intake.ready) _
   let Z_ i X:= S.density R.beta X V • f i X
   have ht (p): Integrable (Z_ p) (prior G _) :=by
     refine StepData.push_slice hz V _ ?_; unfold f; exact ((((team M p).sells H.laws.intake.cap).1.integrable _).const_mul ((raw M p).stock Lt)).smul_const (Verse.controls Z z (raw M p).letters)
   obtain ⟨a,ha⟩:=hz.bound
   have hb i:0≤t i:= (norm_nonneg _).trans (hF i 1)
   have he i X: ‖Z_ i X‖ ≤ a*t i := by
      unfold Z_; rw [norm_smul,Real.norm_of_nonneg (hz.positive ..)]
      exact mul_le_mul (ha ..) (hF ..) (norm_nonneg _) ((hz.positive ..).trans (ha X V))
   have hpP:Summable (fun i=> ∫ x, ‖Z_ i x‖ ∂prior G _):= by
     apply (hp.mul_left a).of_nonneg_of_le (fun i=> integral_nonneg fun _=>norm_nonneg _); intro i
     apply le_trans (integral_mono (ht i).norm (integrable_const (a*t i)) (he i)); simp
   have hk := hasSum_integral_of_summable_integral_norm ht hpP
   have hpV(X): (∑' i,Z_ i X)=S.density R.beta X V • TU X:= by
      exact ((hp.of_nonneg_of_le (fun i=>norm_nonneg _) (fun i=>hF i X)).of_norm.tsum_const_smul (S.density R.beta X V))
   simp_rw [hpV] at hk; let g i := ∫ x,Z_ i x ∂prior G _
   have hQ (p:Finset ι): S.push R.beta (Qf p) V= ∑' j,g (Script.drums M (Script.restrict p) S j):=by
      let h:=Script.drums M (Script.restrict p) S; have he(X): S.density R.beta X V • (Qf p X)=∑ j:Drums (M ∘ Script.restrict p) S,Z_ (h j) X:=by
         unfold Quota TuneR; rw [tsum_fintype,Finset.smul_sum]; refine sum_congr rfl fun i _=> ?_; unfold Z_ f h; rw [Script.docket,Script.letter,Script.clears]
      unfold StepData.push; simp_rw [he]; rw [integral_finsetSum (Finset.univ) (fun i _=>ht (h i)),tsum_fintype]
   rw [show S.push R.beta TU V=∑' i,g i from hk.tsum_eq.symm]; simp_rw [hQ]; exact Serif.tend _ g (show Summable (fun i=>‖g i‖) from hk.summable.norm) (Script.arrived M)

variable [Fintype β]
variable (hx:P'.B=radiusB x) (hp:P'.threshold=Pressure.temp x)(ht:P'.order≤j)(hk:P'.power≤J) (hf:P'.supportExponent≤a)
include hx hp ht hk hf

lemma laws (X:Tree.Forest S.ratio) :
    let F i := Serif.glyph M H χ Z l δ z i V
    Summable F ∧ Summable (BR V) ∧
    S.push R.beta (TU) V= (Complex.ofReal (overhead (prism T x χ o.K V X) R Q.table)) • (GridRenewal.Rain.cyclone (∑' i,F i) * ∑' i,BR V i):= by
   intro FF
   let v:Finset ι→Poly Jm:= fun p=> S.push R.beta (Qf p) V
   have hy:= Serif.chase M H χ Z l δ U h hh z hZ V
   obtain ⟨hF,hV⟩:=Serif.summit M H χ Z l δ U h hh z hZ P' hx hp ht hk V
   obtain ⟨hQ,hS⟩:= Serif.ledger M H χ Z l δ U h hh z hZ H' D P' E₀ V₀ V
   let a:ℂ:= overhead (prism T x χ o.K V X) R Q.table
   refine ⟨hF,hS,tendsto_nhds_unique hy ?_⟩
   refine Tendsto.congr' ?_ (((GridRenewal.Rain.breath.continuousAt.tendsto.comp hV).mul hQ).const_smul a)
   refine Eventually.of_forall fun p=>?_ ; let g:= Script.restrict p; let Z':=(g) ⁻¹' Z
   have hp' := Muse.step (MX p) H χ F' Z' (l ∘ g) δ h.price (Muse.enrolled _ _ _ Z' _ _ U h (Script.scaled M H _ l δ hh)) H' D P' E₀ V₀ hp hx hf (z ∘ g) (fun i=>hZ.square (g i)) X V
   change _= v p; have hv : Qf p=fun X=> ∑ i:Drums (MX p) S,(raw (MX p) i).paint Z' (sits Z' (l∘g) δ) (z∘g) X:=by
      funext V; unfold Quota TuneR; rw [tsum_fintype]
   unfold v; rw [hv]; exact hp'.2.2.symm
end YM.RemainderComparison.Serif
