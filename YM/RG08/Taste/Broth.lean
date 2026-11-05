import YM.RG08.Taste.Phone
/-!
# Returned Wilson matrices as maps between true meshes. Align roots.
Feed from $i+1$ is \pi of push at $i$. In its own $g_i$. Standard first-contact count.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Taste
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {I J:Type} {u:I→Windows}{w:J→ShoreP u}{X:Chain}{G:Gauge}{E e r d τ D j t n k m l :ℕ}{R:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
variable (b: Offer w)
section coupling
variable (X ν D')
lemma forward_none (N i k) : forward X ν D' N i k (0: Native (Letter F))=0 := by
    funext v; change PowerSeries.subst _ 0= _; apply PowerSeries.ext; intro j; simp_rw [ladder, stencilSub]; simp
lemma forward_plus (N i k) (V U:Native (Letter F)) : forward X ν D' N i k (V+U)=forward X ν D' N i k V + forward X ν D' N i k U:= by
    funext b; unfold forward freight; simp only [Pi.add_apply]; exact PowerSeries.subst_add (.of_constantCoeff_zero' (look ..)) ..
end coupling
section order
local notation "F₁" => forward X ν D'
-- calling `Z` arguments in wall
local notation "Τ" => trump T ν D'
local notation "∮" => Ye X ν D' T
local notation "℘" => call H F
variable (T ν D')
-- spans any paid segment not only by lifts. At master means calls leave here in `g_u` and emitted funds priced `g_k`. Restore at bottom.
def freightP (i: Stem w) (V:Native (Letter F)): Native (Letter F):= let z:=i.i; let k:=(w z.a).next.main; let j:=inside i; let n:= b.N z.a; (Τ n j.i k (z.i-j.i)) *ᵥ (F₁ n k j.i V)
abbrev stepsT (i:Wall w 1) : Session (Letter F):= awake (ladder X ν D' (b.N i.a) i.i (w i.a).next.main) ((Te T ν D' (b.part i))⁻¹)
lemma toll_succ (i:Wall w 1)(hj:k<raceL i.low)(V:Native (Letter F)): let q:Stem w:=⟨i.low,k,hj⟩
    freightP ν D' T b ⟨i.roof,k,hj.trans_le (by rw [raceUp];omega)⟩ V=stepsT ν D' T b i *ᵥ (freightP ν D' T b q V) := by
   intro q; unfold freightP; let z:=i.low; let j:=(inside q).i; let N:=b.N i.a; let m:=(w i.a).next.main; let v:=F₁ N m j V
   have hX:j≤ i.i:= along_roof q
   change Τ N j m (i.i+1-j)*ᵥ v= stepsT ν D' T b i *ᵥ (Τ N j m (i.i-j) *ᵥ v)
   rw [show i.i+1-j=i.i-j+1 by omega, mulVec_mulVec]; apply congr_arg (fun A:Session (Letter F)=> A *ᵥ v)
   unfold Pill.trump Pill.firstT; rw [Pill.turn,show j+(i.i-j)=i.i by omega]; rfl
lemma toll_this (i : Wall w 1)(V:Native (Letter F)): freightP ν D' T b ⟨i.roof,raceL i.low,by rw [raceUp]⟩ V= stepsT ν D' T b i *ᵥ (F₁ (b.N i.a) (w i.a).next.main i.i V) := by
   unfold freightP inside; simp_rw [spawn_tip]; change (Τ (b.N i.a) i.i _ (i.i+1-i.i))*ᵥ _= _; rw [show i.i+1-i.i=1 by omega]; unfold Pill.trump Pill.firstT; rw [Pill.turn,Pill.turn,mul_one] -- power simplification names
   rfl
-- at roof with i between; spawn contacts exactly. not pruning on basis read. f_i=D powers push.
def spreads (U:Wall w 1 → Native (Letter F))(t:Wall w 0) : Native (Letter F):=
    ∑ j∈ range (raceL t), if h:j<raceL t then freightP ν D' T b ⟨t,j,h⟩ (U (spawn t j h)) else 0
lemma spread_plus (i: Wall w 1) (U:Wall w 1 → Native (Letter F)):
  spreads ν D' T b U i.roof=stepsT ν D' T b i *ᵥ (spreads ν D' T b U i.low+F₁ (b.N i.a) (w i.a).next.main i.i (U i)) := by
    let G:=stepsT ν D' T b i; rw [Matrix.mulVec_add]; unfold spreads
    -- rw range only in lhs
    rw [show range (raceL i.roof)=range (raceL i.low+1) by rw [raceUp],sum_range_succ, dif_pos (by rw [raceUp]; omega),spawn_tip,toll_this, Matrix.mulVec_sum]; apply congrArg₂ (·+·) ?_ rfl
    refine Finset.sum_congr rfl fun j hj=>?_
    rw [dif_pos (mem_range.mp hj), dif_pos (lt_trans (mem_range.mp hj) (by rw [raceUp]; omega)), ← spawn_same i (mem_range.mp hj)]; exact toll_succ ..
-- residuals and v
variable (U:J→ BoardU D R G)
abbrev phase0 (i : Wall w 0) : ReadsU F D R:= Ye X ν D' T (b.part i)
abbrev curtain (a:J) := eject H (phase0 ν D' T b (Wall.tip w a)) (U a)
abbrev riseV := dawnP ν D' T (b.part (n:=1)) τ (curtain ν D' T b U)
abbrev arcV := route (riseV ν D' T b U) X ν D' (b.part (n:=1)) τ d
abbrev shiftV (i:Wall w 1):= call H F (arcV ν D' T b U i)
abbrev heap (i:Wall w 0) := spreads ν D' T b (shiftV ν D' T b U) i
def offerUp (i:Wall w 0) := F₁ (b.N i.a) i.i (w i.a).next.main (heap ν D' T b U i)
def vMatch (a:J): Native (Letter F):= ℘ (U a)+offerUp ν D' T b U (Wall.tip w a)
def remnant (i:Wall w 0) := riseV ν D' T b U i-edgeBook (phase0 ν D' T b i) (offerUp ν D' T b U i)
local notation "Ⓡ" => remnant ν D' T b U
local notation "Ⓥ" => vMatch ν D' T b U
lemma v_power (i:Wall w 1) (hx:Tights T S ν D' u):
    let P:=arcV ν D' T b U i; let R:=phase0 ν D' T b; let V:= offerUp ν D' T b U
    Needle.push (heights X ν D' (b.part i)) τ d (edgeBook (R i.roof) (V i.roof))=edgeBook (R i.low) (V i.low) + edgeBook (R i.low) (call H F P) := by
   intro P R V; let q:=b.part i; let M:= F₁ (b.N i.a) (w i.a).next.main i.i (shiftV ν D' T b U i); let v:= heap ν D' T b U i.low; let k:=(w i.a).next.main
   rw [epoch_f _ (hx.fair (b.part i)) h ((edge_crew _ _ (hx.firs (b.part i.roof)|>.toBoards) (le_refl d)).1) d hx.hh, ← edge_plus, show V i.roof=F₁ q.N (q.i+1) k (awake (ladder X ν D' q.N q.i k) ((Te T ν D' q)⁻¹)*ᵥ (v+M)) from congr_arg (F₁ (b.N i.a) (i.i+1) k) (spread_plus ν D' T b i _), show V i.low+call H F P=F₁ q.N q.i k (v+M) from ?_] -- arrow?
   rotate_left; · rw [forward_plus]; exact Eq.symm (congr_arg (F₁ q.N q.i k v + ·) (forward_inverse q.N k q.i (shiftV ν D' T b U i))) -- indices
   exact step_basis hx ..
lemma v_opens (j:J) : Ⓡ (Wall.tip w j)=U j-edgeBook (phase0 ν D' T b (Wall.tip w j)) (Ⓥ j) := by
   unfold remnant riseV; rw [openingP]; unfold curtain vMatch eject; rw [edge_plus]; abel
lemma barriers (he:Tights T S ν D' u)(hU:∀ i,Marvel τ (U i))(hp:∀ i,Lank (U i)) : Keeps (riseV ν D' T b U) T ν D' b.part τ := by
  exact dawning he le_rfl (fun _=>rfl) (fun i=>pin H (hU i) (hp i) (he.firs _))
lemma v_steps (i:Wall w 1)(he:Tights T S ν D' u)(hU:∀ i,Marvel τ (U i))(hp:∀ i,Lank (U i)):
    Ⓡ i.low=Needle.push (heights X ν D' (b.part i)) τ d (Ⓡ i.roof) := by
   unfold remnant; rw [lemma_fewer (he.fair _) h ((barriers ν D' T b U he hU hp).zone _).hU ((edge_crew _ _ (he.firs _|>.toBoards) he.hh).1), show riseV ν D' T b U i.low =_ from (barriers ν D' T b U he hU hp).rise i,v_power ν D' T b U i he]; unfold eject
   let S:=phase0 ν D' T b i.low; let g:=arcV ν D' T b U i; let V:=offerUp ν D' T b U
   change g-edgeBook S (call H F g)-edgeBook S (V i.low)=g-(edgeBook S (V i.low)+edgeBook S (call H F g)); abel
lemma v_bottom (i:Wall w 0)(he:Tights T S ν D' u)(hU:∀ i,Marvel τ (U i))(hp:∀ i,Lank (U i)):
    Crop τ (Ⓡ (foothold i)) H F := by
   unfold remnant offerUp heap spreads; rw [show range (raceL (foothold i))=∅ by simp [raceL,foothold], sum_empty, forward_none, edge_none,sub_zero]
   exact (barriers ν D' T b U he hU hp).zone _
end order
end YM.RG08.Taste
