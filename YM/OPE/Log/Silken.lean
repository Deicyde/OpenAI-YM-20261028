import YM.MergeProof.North.Tibetan
/-! # Log-scale affordability of one-time fusion post payment

Strengthens part of `Hymen`, following the `Tibetan` proof.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {X : Targets s K} {D : Rolls s} {Θ : Protection D} {p : Expenses X} {u : Return.Wages} {l : ℕ→ℝ} {P : Teller G}
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe
open MergeProof.Ribbons Graces
section
variable (Q:ConnectedActivityE6.Target G P)(L:Side)(Z:Stage)(d:ℕ)
def modest (x:ℝ) : Prop :=
        (coinFee G Z d L+|2*((L).val:ℝ)^d*(Mercury.volt x Z.order Z.power*((Q).goal L x)⁻¹)|)* Graces.host G Z d≤ betaF G x L
lemma silken : ∀ᶠ x in atTop, modest Q L Z d x:=by
   let f x:=2*(L.val:ℝ)^d*(Mercury.volt x Z.order Z.power*((Q).goal L x)⁻¹)
   have hf: Rate G L (max 0 (-Q.rate)) (fun x=>|f x|):= by
       have hz: Rate G L 0 shiftG:= (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4
       have hp: Rate G L (-Q.rate) (fun x=> (Q.goal L x)⁻¹):=by apply Rate.congr Rate.power; filter_upwards [Delay.shift_pos G L] with x h; exact (Real.rpow_neg h.le _).symm
       have hh: Rate G L (-Q.rate) f:= ((((hz.pow (Z.power*Z.order)).weaken (b:=0) (by simp)).mul_right _|>.mul hp).mul_left _|>.weaken (by linarith)); exact (hh.compare (v:=fun x=>|f x|) (by filter_upwards with x; rw [abs_abs])).weaken (le_max_right ..)
   have he := (((Rate.const (coinFee G Z d L)).weaken (le_max_left ..)|>.add hf).mul_right (host G Z d)) 1 (max_lt zero_lt_one (by linarith only [Q.start]))
   filter_upwards [he] with x hx
   exact (le_abs_self _).trans (hx.trans_eq (Real.rpow_one _))
end
variable (R:Register D p u l) (Q:ℕ→ℕ)
def FrameAccord (X:Targets s K)(D:Rolls s){Θ:Protection D} (T:Delays Θ) : Prop :=∀ j x,T.betaEntry j≤ x →∀ i,StepStages j i→∀ d ≤ i, modest (X j i) (D.L j) (s.profile i) d x
lemma swellFrame (X:Targets s K)(T:Delays Θ) :∃ U: Delays Θ, DelayLe T U∧∀ V:Delays Θ,DelayLe U V → FrameAccord X D V:=by
   obtain ⟨u,-,hv,H⟩:=collect_upper T.betaEntry _ (fun j=> eventually_transitions j _ _ (fun i h=> ((Finset.range (i+1)).eventually_all.mpr (fun d hd=> silken (X j i) (D.L j) (s.profile i) d))))
   exact ⟨{T with betaEntry:=u},⟨hv,le_rfl,le_rfl,le_rfl⟩, fun _ hz j x hx i hi d hd=> H j x ((hz.beta j).trans hx) i hi d (Finset.mem_range.mpr (by omega))⟩
end YM.PhysicalNext.Repeat.Mallow
