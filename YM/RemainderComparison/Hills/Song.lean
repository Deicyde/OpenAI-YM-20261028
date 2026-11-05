import YM.RemainderComparison.Cadence.Universe
import YM.Extra.MULTISOURCE_BOUNDS.Germs
/-!
 # Reprise Actual Φ model while purchasing AUTH. Keep true lengths. κ leaks separate.
  Ordinary ACTION includes HIGH (γ*cubic/quartic) nonlinear completions
 through order two, to correspond to SAME Stamp β* and need no additional
 reset residual. (Value δβ not here.) No assumption about wrapped bilinear
 metric cancellation. -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Hills
open Function Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Geo
open Extra.Iteration WilsonStartup PhysicalNext.Repeat Song Meadow
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {ι : Type} (R : PathData G) (c : Clip) (p : BudgetPoint) {α:Type*}
variable {σ C Λ A u v d a : ℝ} (β γ:ℝ)
open WickReps Musicology
abbrev Stagecraft (n:Side):= Seat n × Rags
def lyric (n:Side)(α:Type*): Manor G n Void α (Stagecraft n):=
    ⟨fun i=>Song.strings R p (Meadow.rollers n i), fun _ i=> Song.sounding R c (β+γ) γ (Meadow.rollers n i), fun _=>0,fun _=>False⟩
local notation "X'"=> Hills.lyric R c p β γ n α
local notation "S'"=> Stagecraft n
variable (h:R.Bounds c σ C Λ) (hp:WilsonStartup.Decent c p)
-- Value.And.Angle.At all x.Probes.Every α.Awards.

def ticket (i:Rags):ℝ:=i.elim (fun t=> mezzo R c p (-γ) t)
         (Sum.elim (fun i=>sine p R.cubic (-(β+γ)) i) (Sum.elim (fun i=>sine p R.quartic (-(β+γ)) i) (fun i=> sine p R.loop (-1) i)))
lemma positive (i:Rags): 0≤ ticket R c p β γ i:=by
    rcases i with i|i|i|i; exact Song.mezzo_pos ..; exact Song.sine_pos ..; exact Song.sine_pos ..; exact Song.sine_pos ..
include h hp
lemma purchased (i:S') : Manor.Sees X' p dust i ∧ ∀ u:α,p.supBounds i.1.2 ((X').halls i) ((X').solvent u i) (ticket R c p β γ i.2):= by
    let T:= ticket R c p β γ
    have hp₁ u : p.Regular ((X').halls i) ((X').solvent u i) ∧ p.supBounds i.1.2 ((X').halls i) ((X').solvent u i) (ticket R c p β γ i.2):=by
       obtain ⟨s,i⟩:=i; rcases i with i|i|i|i
       · exact Song.tally_charge R c p _ (-γ) hp
       · have ht:=Song.pitch_charge p R.cubic (s,i) (-(β+γ)) (fun i=>(h.invariant i).2.1); exact ht
       · exact Song.pitch_charge p R.quartic (s,i) (-(β+γ)) (fun i=>(h.invariant i).2.2)
       exact Song.pitch_charge p R.loop (s,i) (-1) (fun i=>(h.invariant i).1)
    exact ⟨⟨fun i'=> (hp₁ i').1,fun _ j=> isEmptyElim j, fun _ he=>by apply False.elim he⟩,fun u=> (hp₁ u).2⟩
-- native.Q lengths.Exact cover proof through arity-dependent.Y.Support.Weight variant a.L. @ full Step.Clock scope.
omit hp h
open WickReps.Manor
local notation "D'"=> p.power * p.order
local notation "K₁"=> (fun i:Rags=>Meadow.melody R i)
set_option quotPrecheck false
local notation "K'"=> fun j:Stagecraft n=> Meadow.melody R j.2
set_option quotPrecheck false -- K' .2 binder needs before
open Animals
lemma length_b (i:S') (x : Site n) (h:x∈ (X').halls i): separation i.1.2 x≤ p.B+ K₁ i.2 := (neighbors_mem ..).1 (Meadow.yarn R p i.1 i.2 h)
lemma anchor (i:S') (x:Site n) (h:x∈(X').halls i): separation x i.1.2 ≤ p.B * (1+ K₁ i.2) := by
    rw [separation_comm]; have he:= p.B_pos; calc _ ≤ p.B+ K₁ i.2 := length_b R c p β γ (α:=α) i x h
                                                  _ ≤ _ := by rw [Nat.mul_add,Nat.mul_one]; nlinarith
lemma reaping (x:Site n) (i:S') (hx:x∈(X').halls i) : 1+(separation i.1.2 x:ℝ) ≤ (1+(p.B:ℝ))*(1+(K₁ i.2:ℝ)):= by
    have he:=Hills.anchor R c p β γ (α:=α) i x hx; rw [separation_comm x] at he
    refine le_trans (b:=1+(p.B:ℝ)*(1+(K₁ i.2:ℝ))) (add_le_add_right (by exact_mod_cast he) _) ?_; rw [add_mul,one_mul]; gcongr; exact le_add_of_nonneg_right (Nat.cast_nonneg _)
include h hp
lemma funded (i:S')(x:Site n) (hx:x∈(X').halls i) (u:α): p.supBounds x ((X').halls i) ((X').solvent u i) ((1+(p.B:ℝ))^D' * (Hills.ticket R c p β γ i.2)*(1+(K₁ i.2:ℝ))^D'):=by
    let g:= ticket R c p β γ i.2; let a:= i.1.2; let o:= (X').halls i
    obtain ⟨hQ,hF⟩:= purchased R c p β γ (α:=α) h hp i
    have hb:= reaping R c p β γ x i hx; have hg:0≤g:= Hills.positive ..; let v:=(1+(p.B:ℝ))*(1+(K₁ i.2:ℝ)); have hv:1≤v:= (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hb
    refine (VerifiedReset.sup_real (o:=x) (hQ.angle u)).1 ?_
    refine ⟨by change 0≤_*g*_; positivity,fun V hh l hl hd=> ?_⟩
    have ht : (v^p.power)^l.length ≤ (v^p.power)^p.order:= pow_le_pow_right₀ (one_le_pow₀ hv) hl
    refine (Extra.Multi.Germs.relocated_bound (reaping R c p β γ x i hx) ((VerifiedReset.sup_real (o:=a) (hQ.angle u)).2 (hF u)) hh l hl hd).trans ((mul_le_mul_of_nonneg_right ht hg).trans_eq ?_)
    change _= _*g*_; unfold v; rw [← pow_mul, mul_pow]; ring
-- size proof
omit hp

def tickets (G:Gauge)(p:BudgetPoint)(c:Clip)(σ C Λ β γ:ℝ):= host G c p σ C (-γ) + (tenor G 3 p σ C (-(β+γ))+(tenor G 4 p σ C (-(β+γ))+tenor G 2 p σ Λ (-1)))
lemma mezzoRoll (γ:ℝ) : SumBudget (fun i=>Song.mezzo R c p γ i*Real.exp ((σ/2)*i.length R)) (Song.host G c p σ C γ):=by
    convert (Cost.scale (Cost.scale (Geo.low_budget G p R h) (turnFee p*p.threshold^2) (mul_nonneg (turnFee_pos _).le (sq_nonneg _))) |VerifiedReset.factor*γ| (abs_nonneg _)) using 2 with i
    unfold Song.mezzo; ring; rfl -- lint
lemma concord : SumBudget (fun i=> ticket R c p β γ i * Real.exp ((σ/2)* Meadow.melody R i)) (Hills.tickets G p c σ C Λ β γ):=
    Cost.sum (mezzoRoll R c p h _) (Cost.sum (Song.act_lp p R.cubic _ h.width h.three) (Cost.sum (Song.act_lp p R.quartic _ h.width h.four) (Song.act_lp p R.loop _ h.width h.two)))

omit h -- hp omitted
lemma arches (i:S') : (coverNumber p.B ((X').halls i):ℝ) ≤ lowCount+(p.B:ℝ)⁻¹ * Meadow.melody R i.2:= by
    have hb:0<(p.B:ℝ):= Nat.cast_pos.mpr p.B_pos
    have he : p.B*coverNumber p.B ((X').halls i) ≤ p.B*lowCount+ Meadow.melody R i.2:= by
       obtain ⟨s,i⟩:=i
       have ht {l:ℕ} (A:ℕ→Atom G l) (i:ℕ) (he:l≤4): p.B*coverNumber p.B (Song.pitch A (s,i)).support ≤ p.B*lowCount+(A i).length:=by
           change p.B*coverNumber p.B (s.spread _ )≤_; rw [Seat.visit_count]; refine (Wages.traversed (A i) _ p.B p.B_pos).trans ?_; unfold lowCount; nlinarith
       rcases i with i|i|i|i
       · change p.B*coverNumber p.B (s.spread (i.home R p 0)) ≤ _; rw [Seat.visit_count]; exact Geo.low_geometry ..
       · exact ht R.cubic i (by omega)
       · exact ht R.quartic i (by omega)
       exact ht R.loop i (by omega)
    apply le_of_mul_le_mul_left _ hb; rw [mul_add,← mul_assoc,mul_inv_cancel₀ hb.ne',one_mul]; exact_mod_cast he
set_option quotPrecheck false
local notation "σp"=> σ/32
local notation "vp"=> (1+(p.B:ℝ))^D'
def package (p : BudgetPoint) (α σ C:ℝ) := Footprint.payment 1 p.B (p.power * p.order) (σ/32) ((1+(p.B:ℝ))^(p.power*p.order)) (Fintype.card Signed * C) α lowCount
include h hp
lemma sounding (hG : 0 ≤ A) (hF : A/p.B ≤ σ/4) : Breeze.Sonorous p X' K' Set.univ dust A σp (package p A σ (Hills.tickets G p c σ C Λ β γ)):=by
    have hh:=h.width; let v i:= ticket R c p β γ i * Real.exp (σp* Meadow.melody R i); have hv i:0≤v i:= mul_nonneg (positive ..) (Real.exp_pos _).le
    have hp':SumBudget (fun i=> v i * Real.exp ((σ/2-σp)* Meadow.melody R i)) (tickets G p c σ C Λ β γ):=by
       have he : ∀ i,v i*Real.exp ((σ/2-σp) * Meadow.melody R i)=ticket R c p β γ i * Real.exp ((σ/2)* Meadow.melody R i):= fun i=> by unfold v; rw [mul_assoc,← Real.exp_add]; ring_nf
       simp_rw [he]; exact Hills.concord R c p β γ h
    let g (i:S'):= vp* ticket R c p β γ i.2*(1+(K₁ i.2:ℝ))^D'; have hg i: 0 ≤ g i:= by unfold g; have he:= Hills.positive R c p β γ i.2; positivity
    refine ⟨g,hg,fun i _=> ⟨(purchased R c p β γ h hp i).1, fun a x hx=> funded R c p β γ h hp i x hx a⟩,?_⟩
    refine Footprint.assigned id 1 (fun Y : Support n => by simp) (fun i : S' => i.1.2) (fun i=> v i.2) (fun i=> hv _) K' (X').halls (Quotes.channel_anchored _ v hv hp') p.B (D') p.B (Hills.anchor R c p β γ) (arches R c p β γ) (by positivity) ⟨hG,by positivity,?_⟩ (fun i=> g i*Real.exp (σp*K' i)) (fun i=> mul_nonneg (hg _) (Real.exp_pos _).le) (fun i=> le_of_eq (by unfold g v; dsimp only; ring))
    rw [← div_eq_mul_inv]; linarith
end YM.RemainderComparison.Hills
