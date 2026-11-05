import YM.RemainderComparison.Hills.Song
/-!
 # OWN THE STENCILS. Doesn't trade volume for summability through mismatched
  periods. Cofinal.Street. -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Hills
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Geo
open Extra.Iteration WilsonStartup PhysicalNext.Repeat Song Meadow Further.PhysicalPeriodLimitF933 Macrame
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n C : Side} {ι : Type} (R : PathData G) (c : Clip) (p : BudgetPoint) {α:Type*}
variable {σ φ Λ A u v d a : ℝ} (β γ:ℝ)
open WickReps Musicology Animals
abbrev chore (i:Stagecraft n):=Meadow.melody R i.2
def close (b:ℕ):Set (Stagecraft n):={i|chore R i≤b}
def audition (k n':ℕ):Finset (Stagecraft n):= Finset.univ ×ˢ Meadow.ripened R k n'
local notation "s'"=> Hills.audition R
variable (u:α)
local notation "X'"=> Hills.lyric R c p β γ n α
variable {n' k r:ℕ}
lemma eligible (i:Stagecraft n)(hp:i∈ s' k n'): i∈Hills.close R k:= (mem_filter.mp (mem_product.mp hp).2).2
lemma accord (p:Finset (Stagecraft n))(n':ℕ): ∀ᶠ k in atTop,(p:Set (Stagecraft n))∩Hills.close R n' ⊆ (↑(Hills.audition (n:=n) R n' k) : Set (Stagecraft n)) := by
   let Y:= p.filter fun i=> i∈Hills.close R n'; have hp (i:↥Y): ∀ᶠ k in atTop,i.val∈s' n' k:= (Meadow.burgeoning R n' i.val.2 (mem_filter.mp i.prop).2).mono fun k h=> mem_product.mpr ⟨mem_univ _,h⟩
   filter_upwards [eventually_all.mpr hp] with k hk i hi; exact hk ⟨i,mem_filter.mpr hi⟩
variable (S:Finset (Stagecraft n))
variable (he:p.B+k≤ r)
local notation "w"=> Hills.audition R k n'
include he
def supportBasis : Manor.Basis X' (w) r := by
   refine ⟨fun x i=> if x=i.1.2 then 1 else 0, fun x i=>?_, fun i hi=>?_,fun x i hi ht=>?_⟩
   · split; exact zero_le_one; exact le_refl _
   · simp
   by_cases hv:x=i.1.2
   · rw [hv]; exact (Meadow.yarn R p i.1 i.2).trans (Corona.halo_mono ((Nat.add_le_add_left (eligible R i hi) _).trans he) Subset.rfl)
   simp [hv] at ht
include he
-- ν support.Y candidate shares exact. indexing Proof chorus.
lemma sektor (x:Site n) (V:Config G n): (X').sector u (w) (Hills.supportBasis R c p β γ he) x V= Meadow.garner R c (β+γ) γ k n' x V:= by
   unfold Manor.sector Hills.audition; rw [Finset.sum_product,Fintype.sum_prod_type]; dsimp only [Hills.supportBasis]; unfold Meadow.garner
   apply sum_congr rfl; intro s _
   rw [Finset.sum_comm]; apply sum_congr rfl; intro i _; simp_rw [ite_mul,one_mul,zero_mul]; rw [sum_ite_eq, if_pos (Finset.mem_univ x)]; rfl -- edit
variable (h:R.Bounds c σ φ Λ) (hp:WilsonStartup.Decent c p)
include h hp
lemma locale (x:Site n) : LocalOn (neighbors r x) ((X').sector u w (Hills.supportBasis R c p β γ he) x):= by
    intro U V hx
    apply sum_congr rfl; intro i hi; let A:= supportBasis R c p β γ he (n':=n') (n:=n) (α:=α)
    change A.support x i * _ =_
    by_cases hp': A.support x i=0
    · change _= A.support x i *_; rw [hp',zero_mul,zero_mul]
    apply congr_arg (A.support x i*·)
    exact (purchased R c p β γ h hp i).1.angle u|>.sites U V (agrees_mono hx (Finset.coe_subset.mpr (A.location x i hi hp')))
omit hp h
lemma twins (s:Signed)(i:Site n)(x:Site n)(U :Config G n): (X').sector u w (Hills.supportBasis R c p β γ he) x (pull s i U) = (X').sector u w (Hills.supportBasis R c p β γ he) (affine s i x) U:= by
    rw [Hills.sektor,Hills.sektor]; unfold Meadow.garner
    conv_rhs=> rw [← Equiv.sum_comp (Equiv.mulLeft s)]
    apply sum_congr rfl; intro j _; apply sum_congr rfl; intro k _
    have hp := congr_fun (Seat.view_move (G:=G) (j,x) s i) U
    rcases k with h|h|h|h <;> first | (exact congr_arg (fun V=>VerifiedReset.factor*(-γ)*(h.mark R c * h.plain R (0:Site n) V)) hp.symm) | (exact congr_arg (fun V=>VerifiedReset.factor*(- (β+γ)) * (R.cubic h).unmasked V 0) hp.symm) | (exact congr_arg (fun V=>VerifiedReset.factor*(- (β+γ)) * (R.quartic h).unmasked V 0) hp.symm) | (exact congr_arg (fun V=>VerifiedReset.factor*(-1) * (R.loop h).unmasked V 0) hp.symm)

local notation "T₁"=> Stagecraft C
local notation "V'"=> Hills.lyric R c p β γ C α
local notation "w₁"=> Hills.audition (n:=C) R k n'
set_option quotPrecheck false
local notation "Sx"=> (X').sector u w (Hills.supportBasis R c p β γ he)
local notation "Sy"=> (V').sector u w₁ (Hills.supportBasis R c p β γ he)
include hp h
variable (hz:2*(r+1)<n.val)(hC:2*(r+1)<C.val)
open Trio Slide
include hz
lemma crossbrace (x:Site n)(y:Site C)(U: Config G n)(V:Config G C)(hx:Agrees (Lattice.box r) (expandAt x U) (expandAt y V)) : (Sx) x U=(Sy) y V:=by
    let Q:= n*C; let ℋ:= normal (Deck.divides (show Q.val=n.val*C.val from rfl)) rfl; let U':= normal (Deck.divides (show Q.val=C.val*n.val from mul_comm ..)) (show Q.val=C.val*n.val from mul_comm ..)
    let W:= Hills.lyric R c p β γ Q α; let b:= (W).sector u (Hills.audition R k n') (supportBasis R c p β γ he) 0
    let v₀:=translate x U; let u₀:=translate y V
    have hq: b (ℋ.links v₀)= Sx x U:= by
        unfold b W; rw [Hills.sektor,Meadow.garner_pack]; unfold v₀; rw [map_zero,← Hills.sektor R c p β γ u he, ← Lattice.pull_one,Hills.twins]; simp [affine] -- affine simp
    have hm:b (U'.links u₀)=Sy y V:= by
        unfold b W; rw [Hills.sektor,Meadow.garner_pack]; unfold u₀; rw [map_zero,← Hills.sektor R c p β γ u he, ← Lattice.pull_one,Hills.twins]; simp [affine]
    rw [← hq,← hm]; have ht: 2*(r+1)<Q.val := lt_of_lt_of_le hz (Nat.le_mul_of_pos_right _ C.pos)
    apply locale R c p β γ u he h hp 0 _ _ (Slide.readNear 0 ht ?_)
    rw [Slide.rolls,Slide.rolls,map_zero,map_zero]; unfold v₀ u₀; rw [Slide.increases,Slide.increases]; exact hx
end YM.RemainderComparison.Hills
