import YM.RemainderComparison.Hills.Loans

/-!
# Rehearse calibration perturbation

Completely masked short potentials plus Hiss (outcomes with actual flag
witness), exact. No affine null promised. Hiss will appear in a single Flues
calculus along with post projections, not spending path decay for a missing
kappa reserve.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Dove
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Geo Lacuna Ethereal Animals
open Extra.Iteration WilsonStartup PhysicalNext.Repeat Song Meadow Further.PhysicalPeriodLimitF933 Macrame
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n C : Side} {ι : Type} (R : PathData G) (c : Clip) (p : BudgetPoint) {α:Type*}
variable {σ φ Λ A u v d a : ℝ} (β γ:ℝ)
abbrev Rags := VerifiedReset.Low ⊕ ℕ ⊕ ℕ -- inspect
abbrev Jig (n : Side) := Seat n × Dove.Rags
abbrev Twill (n:Side) := Faces n ⊕ Stave (n:=n) ⊕ Stave (n:=n)

def station (n : Side) : Jig n≃ Twill n:= (Equiv.prodSumDistrib _ _ _).trans (Equiv.sumCongr (Equiv.refl _) (Equiv.prodSumDistrib _ _ _)) -- test

def cliff (n : Side): Vowel G n (Twill n):= ⟨Sum.elim (lowEntry G R p) (Sum.elim (pitch R.cubic) (pitch R.quartic)), Sum.elim (tuneLow R c γ) (Sum.elim (tuneAtom R.cubic γ) (tuneAtom R.quartic γ))⟩
local notation "Cʼ"=> cliff R c p γ n

def cascade (n : Side): Vowel G n (Jig n) := ⟨(cliff R c p γ n).sign∘(station n),(cliff R c p γ n).stanza∘station n⟩
local notation "Vʼ"=> Dove.cascade R c p γ n

local notation "Hx"=> Hills.breeze R c p γ n

-- True width decorative_length for analyst.Larger address costs require admission posture.
def weight (i:Rags):ℝ:= i.elim (Song.mezzo R c p γ) (Sum.elim (Song.sine p R.cubic γ) (Song.sine p R.quartic γ))
lemma stamp (i:Rags):0≤ weight R c p γ i:=by rcases i with i|i|i; exact mezzo_pos ..; exact sine_pos ..; exact sine_pos ..
def length (i:Rags):ℕ:= i.elim (fun j=> j.length R) (Sum.elim (fun j=> (R.cubic j).length) (fun j=> (R.quartic j).length))
def taper (σ C:ℝ):= host G c p σ C γ+ (tenor G 3 p σ C γ+tenor G 4 p σ C γ)

variable (i:Jig n)(s : Signed)(x:Site n) (V: Config G n)
set_option maxHeartbeats 800000 in
lemma spins : (Vʼ).sign (whirl s x i) = Song.line ((Vʼ).sign i) (s,x) ∧ weight R c p γ (whirl s x i).2 = weight R c p γ i.2 ∧ (Vʼ).stanza (whirl s x i)=(Vʼ).stanza i ∘ pull s x:=by
    let S : Seat n:= (s,x)
    have hp:= i.1.view_move (G:=G) s x
    have he (Y : Support n)(hp : (0:Site n)∈Y): (Seat.move s x i.1).reg Y hp = Song.line (i.1.reg Y hp) S:=by
       have hh:= i.1.spread_move s x Y
       exact (Ethereal.lineTest (show ((Seat.move s x i.1).reg Y hp).site=affine s x (i.1.reg Y hp).site from rfl) hh).symm
    obtain ⟨t,i⟩:=i; rcases i with i|i|i
    · refine ⟨he _ (Low.small_home ..),rfl,funext fun W=>?_⟩; exact congr_arg (fun U => VerifiedReset.factor*γ * (i.mark R c*i.plain R (0:Site n) U)) (congr_fun hp W)
    · exact ⟨he ((R.cubic i).footprint (0:Site n)) (Finset.mem_image.mpr ⟨0,mem_insert_self ..,by simp⟩),rfl,funext fun W=>congr_arg (fun U=> VerifiedReset.factor*γ*(R.cubic i).unmasked U 0) (congr_fun hp W)⟩
    exact ⟨he ((R.quartic i).footprint (0:Site n)) (Finset.mem_image.mpr ⟨0,mem_insert_self ..,by simp⟩),rfl,funext fun W=>congr_arg (fun U=>VerifiedReset.factor*γ*(R.quartic i).unmasked U 0) (congr_fun hp W)⟩
variable (h:R.Bounds c σ φ Λ) (hp:WilsonStartup.Decent c p)(hw:Geo.Width p c σ)
include h hp hw
set_option maxHeartbeats 600000 in
lemma essence : HasSum (fun i:Jig n => (Vʼ).ray p i V) (R.inChannels c p (β+γ) V-R.inChannels c p β V-(Hx).canopy V):=by
   let F i:= (Cʼ).ray p i V
   rw [Song.chan,Song.chan]; have hx:= Hills.gliding R c p γ h hp hw V
   have hE: HasSum F (γ*Collection.receipt R c p V+(γ*Song.billOf p R.cubic V+γ*Song.billOf p R.quartic V)) := HasSum.sum (f:=F) (Song.pasted R c p V γ h) (HasSum.sum (f:=fun i=> F (.inr i)) (Song.allocated p R.cubic V γ h.width h.three) (Song.allocated p R.quartic V γ h.width h.four))
   have he := (station n).hasSum_iff.mpr hE
   -- no convert too much
   let U:= averaged fun s=>∑ i:Pressure.Cell n,R.baseTerm c p (pull s 0 V) i -- name
   change HasSum _ ( (β + γ)*U+_-(β*U+_)-(Hx).canopy V ); rw [show (β+γ)*U+((β+γ)*(Song.billOf p R.cubic V+Song.billOf p R.quartic V)+Song.billOf p R.loop V)-(β*U+(β*(Song.billOf p R.cubic V+Song.billOf p R.quartic V)+Song.billOf p R.loop V))-(Hx).canopy V =γ*Collection.receipt R c p V+(γ*Song.billOf p R.cubic V+γ*Song.billOf p R.quartic V) from ?_]; exact he
   unfold U; linarith only [hx]

omit hw
-- σ≥0 heights may choose arbitrary Bp at output as long as admitted.This is BEFORE inter-clock Consumer asks. PAY anchored addresses.
lemma land : p.Regular ((Vʼ).sign i).support ((Vʼ).stanza i) ∧ p.supBounds ((Vʼ).sign i).site ((Vʼ).sign i).support ((Vʼ).stanza i) (weight R c p γ i.2):=by
    obtain ⟨s,i⟩:=i; rcases i with i|i|i; exact Song.tally_charge R c p (s,i) γ hp; exact Song.pitch_charge p R.cubic (s,i) γ (fun j=>(h.invariant j).2.1); exact Song.pitch_charge p R.quartic (s,i) γ (fun j=>(h.invariant j).2.2)
omit hp h
def appears (i:Rags): Meadow.Rags:= (Sum.map id (Sum.map id Sum.inl)) i -- check
lemma reach : ((Vʼ).sign i).support⊆ neighbors (p.B+ length R i.2) i.1.2:=by
   obtain ⟨s,i⟩:=i; have hh:= Meadow.yarn (c:=n) R p s (appears i); rcases i with i|i|i<;>exact hh
set_option quotPrecheck false
lemma lengths' : (coverNumber p.B ((Vʼ).sign i).support:ℝ) ≤ lowCount+(p.B:ℝ)⁻¹ * length R i.2:=by
   obtain ⟨s,i⟩:=i; have hh:= Hills.arches (α:=Unit) R c p γ γ ((s,appears i):Hills.Stagecraft n); rcases i with i|i|i <;> exact hh
include h
lemma enrol : SumBudget (fun i=>weight R c p γ i * Real.exp ((σ/2)*length R i)) (Dove.taper (G:=G) c p γ σ φ) := Cost.sum (Hills.mezzoRoll R c p h _) (Cost.sum (Song.act_lp p R.cubic _ h.width h.three) (Song.act_lp p R.quartic _ h.width h.four))
set_option maxHeartbeats 500000 in
lemma eons (τ η:ℝ)(ht:0≤ τ) (he:η + τ/p.B ≤ σ/2) : ∀ j:Site n, SumBudget (fun i:Jig n=> if ((Vʼ).sign i).site = j then weight R c p γ i.2 * Real.exp (η * length R i.2) * Real.exp (τ* coverNumber p.B ((Vʼ).sign i).support) else 0)
       (Real.exp (τ*lowCount) * (Fintype.card Signed * Dove.taper (G:=G) c p γ σ φ)):=by
    let f i:= weight R c p γ i*Real.exp ((σ/2)*length R i)
    have hp (i:Jig n) : ((Vʼ).sign i).site=i.1.2:=by obtain ⟨s,i⟩:=i; rcases i with i|i|i<;>rfl
    intro j; have hf:∀ i,0 ≤ f i:= fun i=> mul_nonneg (stamp ..) (Real.exp_pos _).le
    let L(i:Rags):=length R i
    have hu := Cost.scale (Quotes.channel_anchored (fun (_:Rags)=>0) f hf (show SumBudget (fun i=> f i*Real.exp ( (0:ℝ)*((fun (_:Rags)=> (0:ℕ)) i:ℝ))) (Dove.taper (G:=G) c p γ σ φ) from (by simp; exact enrol R c p γ h)) j) _ (Real.exp_pos (τ*lowCount)).le -- shape
    apply budget_mono hu
    · intro i; split; exact mul_nonneg (mul_nonneg (stamp ..) (Real.exp_pos _).le) (Real.exp_pos _).le; exact le_rfl
    intro i; dsimp only; by_cases h:i.1.2=j
    · rw [hp i,if_pos h,if_pos h]; dsimp only [f]; rw [mul_left_comm, zero_mul,Real.exp_zero,mul_one,mul_assoc,mul_assoc,← Real.exp_add,← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (stamp ..); apply Real.exp_monotone; rw [div_eq_mul_inv] at he; nlinarith only [mul_le_mul_of_nonneg_left (lengths' R c p γ i) ht,mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (α:=ℝ) (length R i.2))]
    rw [hp i,if_neg h,if_neg h,mul_zero]
end YM.RemainderComparison.Dove
