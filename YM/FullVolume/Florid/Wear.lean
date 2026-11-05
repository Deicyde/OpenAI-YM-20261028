import YM.FullVolume.Florid.PondT
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Eco
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire.Imago
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray Daisy Lotus
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R}
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' f':ℝ} {K:ℕ} {χ:Chi}
open Lyre Jams
set_option quotPrecheck false
variable {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K)
open Merge Tickets Merge.Palette Lyre Tune
namespace Crew
-- authentic epochs.affine Camera geometry. φ held input hats all.FULL.Reached.
variable {A:Type}[Fintype A](V:A→Mill U)
open Daisy PhysicalNext.Repeat.Greenbelt PhysicalNext.Repeat.Jams Ovens
variable (p:Tickets (sign (faces V) S))
local notation "V₁"=> Merge.Palette.team (faces V) p
local notation "Λ"=>U.pole
local notation "T₀"=> radiusB x₀
local notation "Q'" => Empire.stella Q
variable {ν α:ℝ} {s:Lyre.Signal 0} (hc:Clear Q L μ ν x₀ v s)(hr: Lyre.Clarity H 0 C δ ν)(hσ:Margin G L x₀ α δ)(hv:2≤v)
variable (X:Coat T F)(he:X.x=x₀)(ht:X.width=o.K)
variable (i:Molecule S)
local notation "f₀"=> U.plainP s ν
local notation "f₁"=> U.totalP s ν
local notation "d" => pleas V p α ν s i
variable (Cy:A→ℝ)(hh:∀ i,0≤Cy i)
local notation "A₀"=>accountK V Cy s
open Merge Switch FullVolume.Ray.Weigh
open Gas Ursell Trees Multiple Letter OmitClusters
set_option quotPrecheck false
open Mill Match Ovens Ovens.Pipes Refrain
-- input separate mark postage by canonical corona; sum over extra OCC valuations at Probe (not Shirley caps). Compass.S
abbrev extra (Cy:A→ℝ) := Tickets.extra (Palette.mark (c:=c) (faces V)) (Palette.wages (faces V) Cy)
def Pave (V:A→Mill U) (Cy:A→ℝ) :Prop:= (∀ i,0 ≤ Cy i) ∧ Ac.Hit H.birth (radiusB x₀) (Reserves.tariff (Crew.extra (c:=c) V Cy) (ConnectedActivityE6.lengths T R) (fun _=>0) Q.ε) Q.relative (Daisy.ribbon Q' L x₀)
lemma PayHead (V:A→Mill U) (Cy:A→ℝ) (h:Pave V Cy) (hc:Clear Q L μ ν x₀ v s): Mixed.Accounts S Q.halo (radiusB x₀) (Daisy.swing (stella Q) L μ R.beta x₀ ν) H.birth (accountK V Cy s) (ConnectedActivityE6.lengths T R) (steamP S ((Empire.stella Q).costs L μ R.beta x₀ ν)):=by
   let K0:= (stella Q).costs L μ R.beta x₀ ν; let M0:=U.receipt s (H.alarms*topStorm S.patch); have hz := (U.furnace s).raise hc.shill
   have hp : Mixed.Accounts S Q.halo (radiusB x₀) K0 H.birth M0 (ConnectedActivityE6.lengths T R) (steamP S K0):= ⟨fun i _=> ⟨mul_nonneg zero_le_one (Real.exp_pos _).le,le_rfl⟩,hz.nonneg,fun _=>Nat.cast_nonneg _,hz.hit⟩
   have hh i:0 ≤ Crew.extra V Cy i:=Finset.sum_nonneg fun j _=> by split; exact mul_nonneg (h.1 j) (V j|>.pole.profit); rfl
   refine ⟨hp.packetBound,fun i=>add_nonneg (hp.holds i) (hh i),hp.extra,fun i=>?_⟩
   convert! budget_plus (hp.pays i) (h.2 i) using 1; ext j; split; next h=>
    unfold Reserves.tariff; rw [show accountK V Cy s j=M0 j+ Crew.extra V Cy j from rfl]; simp only [add_mul]; rfl
   next=> simp
structure Wield (χ:Chi) (V:A→ Mill U) (Cy:A→ℝ) (e u v':ℝ) : Prop where
   salary : ∃ f, Ac.Hit (fun i:H.fragrances=>H.bookFoot (.inr i)) (radiusB x₀) f e u ∧ ∀ i, Strung (fun t U=>songK χ V Cy t U i) (v/2) (f i)
   bones : ∃ f, Ac.Hit H.library (radiusB x₀) f e v'∧∀ i,Strung (fun t=>spine χ V Cy t i) (v/2) (f i)
include V hc hr hσ hv in -- no Y fix
lemma carries (hA:(Daisy.swing (stella Q) L μ R.beta x₀ ν).Buy S.patch.L Q.halo (radiusB x₀))(hp:0 < scoreD Q L μ x₀){e:ℝ}(he:e+3*α≤Q.exp)(hx:0 ≤ e)(hB:figureS Q L μ x₀≤ 1/2) (hK : degreePrice (radiusB x₀) (figureS Q L μ x₀) α≤1/2) (χ:Chi)(Hh:Pave V Cy) : Wield χ V Cy e ((2*scoreD Q L μ x₀)*(1-1/2)⁻¹) (Crew.zerosV Q L μ x₀):=by
    have hY:= PayHead V Cy Hh hc; have hh:= Hh.1
    refine ⟨⟨Crew.grading V Cy α ν s,fun i=>?_,columnK χ V hc hr hσ hv Cy hh⟩,_,Crew.grange V Cy hh hY hA hp he hx hσ.hp hB hK, fun i=> ?_⟩
    · let F:= fun i:H.ThinP=> laude V Cy 0 α ν s i.val; let n:= 2* scoreD Q L μ x₀
      have hf(i):0 ≤ F i:=crestK V _ _ Cy hh
      have hh: Trees.Ready H.smallAt (radiusB x₀) F e n α (1/2):=by
         refine ⟨mul_pos zero_lt_two hp,hσ.hp,?_ ,(by norm_num),hf,fun i=>?_⟩
         · apply le_trans ?_ hK; unfold degreePrice Trees.stretch; unfold n figureS; have ht := hσ.hp; gcongr; norm_num
         have hp:= budget_pull (fun i:H.ThinP=>i.val) Subtype.val_injective (foes V Cy hh (α:=α) hY hA 0 i)
         refine budget_mono hp (fun i=>?_) fun p=>?_
         · split
           · exact mul_nonneg (hf _) (Real.exp_pos _).le
           exact le_rfl
         split
         next hv=> rw [if_pos (show i∈ H.unionP p.val from hv)]; apply mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (hf p); exact mul_le_mul_of_nonneg_right (by linarith [hσ.hp]) (show 0≤ (coverNumber T₀ (H.smallAt p):ℝ) from Nat.cast_nonneg _)
         next h=> exact hp.1 _
      have he:= Ursell.log_hit_tail _ _ _ H.testS hh hx 0 i; rw [pow_zero,mul_one] at he; convert! he using 2;rename_i j
      simp only [Nat.zero_le,true_and]; exact rfl
    exact bluff χ V hc hr hσ hv Cy hh i
-- uniform purchases at fixed Query & any Foam assumption (L required for Pave, not here). exponents after.F. returns e halo. sup. ≤ Funding.Bill.*
lemma freshVeil (Q:Target G P) (hQ: Q.rate ≤ -(7/16:ℝ))(L:Side)(μ:ℝ)(hμ:0<μ)(W:ℝ)(o:Target.Order G W)(C:ℝ)(χ:Chi) (e:ℝ)(he:0 ≤ e)(hx:e<Q.exp) : ∀ᶠ x in atTop,∀ (c f:Side) (S:StepData c f)(R:Rep G f)(T:Tube G S)(H:Cash W x μ L Q o C T R) (U:Tune H (fire G L x) (thaw G L x)), ∀ (A:Type)[Fintype A](V:A→Mill U) Cy, Pave V Cy → Wield χ V Cy e (pottery G L x) (Real.exp (-Q.mark L μ x)):=by
   obtain ⟨ν,hν,hz,h₀,hT⟩:= crown G L 0 0 C; obtain ⟨s₀⟩:= Lyre.signed_signal 0
   have hp: Rate G L (stella Q|>.rate) (scoreD Q L μ):= (Daisy.strides L (stella Q) hμ 0).1
   have hu:Rate G L (stella Q|>.rate) (figureS Q L μ):=hp.mul_left _
   let α:= (Q.exp-e)/3; have hs:0<α:=by unfold α; linarith
   have hd : Rate G L (stella Q|>.rate) (fun x=> degreePrice (radiusB x) (figureS Q L μ x) α):=by
       unfold degreePrice Trees.stretch; simp_rw [div_eq_mul_inv]; have he:= Census.width_rate G L 1 0; simp only [one_mul, add_zero] at he; simpa only [zero_add] using! (((he.mul hu).mul_right α⁻¹).mul_left 4)
   have ha:(stella Q).rate<0:= (stella Q).stop
   filter_upwards [hu.below ha (1/2) (by norm_num),shows Q L μ h₀ s₀ hμ hQ, sailsW (L:=L) (stella Q) hμ, hd.below ha (1/2) (by norm_num), pocketsC G L hs, ((tendsto_rpow_atTop (show (0:ℝ)<1/256 by norm_num)).comp (Work.E09.betaF_growth G L)).eventually_ge_atTop 2, (((hp.mul_left (2:ℝ)).mul_right ((1-1/2)⁻¹:ℝ)) (-(3/8)) (by change -(2/5:ℝ)< -(3/8); norm_num))] with x he₀ hC hV hp' ht hS hv c f S R T H U A hI V Cy h
   have hZ := H.laws.data.funds.length_eq
   have hc : R.beta∈Set.Ici (betaF G x L/2):=by have hp:= H.laws.intake.window.1; rw [hZ] at hp; exact hp
   have he':(Daisy.swing (stella Q) L μ R.beta x ν).Buy S.patch.L Q.halo (radiusB x):= hZ.symm ▸ hV _ _ (hC.forcer _ hc)
   have hh : Lyre.Clarity H 0 C (thaw G L x) ν:= ⟨fun F X m hh ha=> hT c f S T F X m x _ _ C hz le_rfl hh H.laws.data.funds.length_eq ha U.pole.full.2.2 U.pole.active⟩
   have hb : figureS Q L μ x≤ 1/2:=(le_abs_self _).trans he₀
   have hg : 0<scoreD Q L μ x:=by
           unfold scoreD Mixed.Costs.ceiling; have ht := he'.γ; have he:= he'.grows; have hB: (1-(Daisy.swing (stella Q) L μ R.beta x ν).q)>0:=by linarith -- unfold
           unfold Reserves.extract Reserves.treeYield; -- align.C
           let a:=Daisy.swing (stella Q) L μ R.beta x ν; change 0<polyPrice a.reservePoly 0 * _ * (a.rootHit * _ * (1-a.q)⁻¹); change a.rootHit>0 at ht;change 1-a.q>0 at hB;unfold polyPrice; positivity
   obtain ⟨⟨a,hA,hQ⟩,⟨b,hB,hq⟩⟩:= Crew.carries (ν:=ν) V hC hh ht (show 2≤fire G L x from hS) Cy he' hg (show e+3*α≤Q.exp from by unfold α; linarith) he hb ((le_abs_self _).trans hp') χ h
   refine ⟨⟨a,fun i=>budget_loosen (hA i) ((le_abs_self _).trans hv),hQ⟩,b,fun i=>budget_loosen (hB i) ?_,hq⟩
   unfold Crew.zerosV; refine mul_le_of_le_one_right (Real.exp_pos _).le ?_; rw [show (1-1/2:ℝ)⁻¹=2 from by norm_num]; linarith
end Crew
end YM.ConnectedActivityE6.Empire.Imago
