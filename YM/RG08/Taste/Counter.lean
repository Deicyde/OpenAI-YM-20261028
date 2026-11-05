import YM.RG08.Pivot.Worth
import YM.RG08.Taste.Table
/-!
# Top-encoded Wick read on arbitrary compensated source. Proof on analytic normalized
formal jets only. Matrices use our previous pivot certificates.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Taste
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries Drift Pivot
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {I J W:Type} {u:I→Windows}{w:J→ShoreP u}{X:Chain}{G:Gauge}{E e r d τ D j t n k m l :ℕ}{R:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}{T':Aperture G P k E τ d D R}
variable (b:Offer w)(T ν D')
abbrev prefixT (i:Wall w 0) := trump T ν D' (b.N i.a) (w i.a).low (w i.a).next.main (raceL i)
lemma billP0 (i:Wall w 1): prefixT ν D' T b i.roof=stepsT ν D' T b i * prefixT ν D' T b i.low:= by
    unfold prefixT; rw [raceUp]; unfold Pill.trump firstT; rw [turn]; change Pill.awake (ladder X ν D' _ ((w i.low.a).low+raceL i.low) _) ((dice X ν D' _ _ _ _ _ ((w i.low.a).low+raceL i.low))⁻¹) * _= _; rw [raceH]; rfl
abbrev upside (U:BoardU D R G)(M : Row (Loc G 1) (Loc G 1))(τ:ℕ)(H:Hol G)(F:Labels.Frame G d) := fun (i:Letter F)=> invest H (frisk M (U 0) τ (slot i)) i
abbrev vCook  (_ :Signals P Q E τ H Ω h hD) (i:Wall w 0)(U:BoardU D R G):= upside U (fires X G (b.N i.a) i.i) τ H F
lemma vCook_tex (i:Wall w 1)(U:BoardU D R G)(ht:Marvel τ U)(hU:Lank U)(he:Tights T S ν D' u):
    let t:= b.part i; let Y:= diagonalSl (hot (Te T ν D' t) 0)
    vCook b T i.low (Needle.push (heights X ν D' t) τ d U)=Y *ᵥ (vCook b T i.roof U) := by -- T inferred?
    intro t Y; ext1 j; let W:= frisk (fires X G t.N (t.i+1)) (U 0) τ (slot j); let V:BoardU D R G:=Needle.push (heights X ν D' t) τ d U
    let x:= X.flight t.N t.i; obtain ⟨_,_,B⟩:=portion G X.kernel.penalty_pos (X.adm (t.i+1)); let g i:= frisk (fires X G t.N (t.i+1)) (U 0) τ i
    have hv : Gold W :=gold_sum (G:=G) (a:=range (τ+1)) (r:=slot j) fun v _=> golden_terraces X.kernel.penalty_pos (X.adm (t.i+1)) (W:=U 0) (fun m=> sober_vetted ht) (X.history t.N (t.i+1)) (slot j) v
    have hx : Polished (g (slot j)):= polished_sum (fun v _=> pol_front (U:=U 0) (B _|>.1) (hU 0) v _)
    have hJ:d≤ X.J (t.i+1):= (Nat.le_add_right ..).trans (he.he.stepCap t.up.toLaunch)
    change invest H (frisk (fires X G t.N t.i) (V 0) τ (slot j)) _= _
    have heq : frisk (fires X G t.N t.i) (V 0) τ (slot j)=aboard d (painted G (Carrier.linesOf x X.kernel.penalty)) W:= lint_aware X ν D' h he.hv he.hz U τ d ht hU t.cut _
    rw [heq, projection_prime H x X.kernel.penalty_pos (X.adm _) hJ h hv hx j rfl he.sound he.pop (d.le_succ.trans hD), Finset.sum_filter]; unfold mulVec dotProduct; refine Finset.sum_congr rfl fun p vp=>?_
    unfold Y diagonalSl; simp only [Matrix.of_apply]; split_ifs with H' H'
    · obtain ⟨Z,hZ,hX⟩:= demandPrint X ν D' P he.hv he.hz t.N t.i t.cut
      rw [show leadingV _ _ _ _ _ _ _ _=hot (Te T ν D' t) 0 j p from (arch_turn H x X.kernel.penalty Z (dance X ν D' t.N t.i) X.kernel.penalty_pos (X.adm _) hJ (he.fair t) h he.sound he.pop _ hZ hX (he.firs t.up) p j (by omega)).symm]; apply congr_arg (hot (Te T ν D' t) 0 j p *·); change invest H (g _) _=invest H (g _) _; congr 1; rw [H']
    all_goals first|omega|rw [zero_mul]
-- declaration vCook did not include T? fix
lemma skit (i:Wall w 1): hot (stepsT ν D' T b i) 0=hot ((Te T ν D' (b.part i))⁻¹) 0:= by
    ext x j; simp [stepsT,Pill.awake, ladder, hot_node,stencilSub]
-- pure Leib inverse orientation. Diagonal along prefix only, matrix NOT truncating any e.
def breathP (i:Wall w 0): Loft F := diagonalSl (hot (prefixT ν D' T b i) 0)
local notation "Θ" => breathP ν D' T b
private lemma h_div (i:Wall w 0)(h:LitP (1:Loft F)) (hX:Tights T S ν D' u) : LitP (hot (prefixT ν D' T b i) 0):= by
    generalize hv:raceL i=n; induction n generalizing i with
    | zero => rw [prefixT,hv,Pill.trump,firstT,turn,hot_one,if_pos rfl]; exact h
    | succ n ih=>
      have hh:i.i>(w i.a).low:= by have he:=raceH i; omega
      let z : Wall w 1:=⟨i.a,i.i-1,by omega,by have he:=i.last; omega⟩
      have hZ: z.roof=i:= by obtain ⟨a,j,H,H'⟩:= i; unfold Wall.roof z; dsimp only; congr 1; change j>_ at hh; omega
      have hE: raceL z.low=n:= by rw [← hZ,raceUp] at hv; omega
      have ht':= ih z.low hE
      rw [← hZ,billP0, hot_m0,skit]; intro i j h'; rw [Matrix.mul_apply] at h'; obtain ⟨p,_hp,H⟩:= exists_ne_zero_of_sum_ne_zero h'; obtain ⟨ht,hb⟩:= mul_ne_zero_iff.mp H; exact ((blazing (hX.reads (b.part z)).1).1 i p ht).trans (ht' p j hb)
lemma skit_b (i:Wall w 0) {U:Wall w 0→ Letter F→ℝ}(he : Tights T S ν D' u)
  (hU:∀ i:Wall w 1,U i.low=diagonalSl (hot (Te T ν D' (b.part i)) 0) *ᵥ U i.roof): U i= Θ i *ᵥ U (foothold i) := by
    generalize hv:raceL i=n; induction n generalizing i with
    | zero=>
      have hF:foothold i=i:= by obtain ⟨a,j,h,h'⟩:=i; unfold foothold; dsimp only; congr 1; have he:=raceH (w:=w) (⟨a,j,h,h'⟩); rw [hv] at he; exact he
      rw [breathP,prefixT,hv,hF,Pill.trump,firstT,turn,hot_one,if_pos rfl,show diagonalSl (1:Loft F)=1 from ?_,one_mulVec]
      ext x j; by_cases hx:x=j <;> simp [diagonalSl,hx,Matrix.one_apply]
    | succ n ih=>
      have hh:i.i>(w i.a).low:= by have he:=raceH i; omega
      let z : Wall w 1:=⟨i.a,i.i-1,by omega,by have he:=i.last; omega⟩
      have hZ:z.roof=i:= by obtain ⟨a,j,H,H'⟩:= i; unfold Wall.roof z; dsimp only; congr 1; change j>_ at hh; omega
      have hE: raceL z.low=n:= by rw [← hZ,raceUp] at hv; omega
      have hr : LitP (1:Loft F):= fun i j h=> (le_of_eq (congr_arg (slot (F:=F)) (of_not_not (fun h'=> h (Matrix.one_apply_ne h'))))) -- classical
      have ht:= h_div ν D' T b z.low hr he
      have hT:= he.reads (b.part z)|>.1
      rw [← hZ,breathP,billP0,hot_m0,skit, horiz (blazing hT|>.1) ht, ← Matrix.mulVec_mulVec,show foothold z.roof=foothold z.low from rfl, show diagonalSl (hot (prefixT _ _ T _ z.low) 0)*ᵥ U (foothold z.low)= _ from (ih z.low hE).symm,hU z,mulVec_mulVec,show diagonalSl (hot ((Te T ν D' (b.part z))⁻¹) 0)*diagonalSl (hot (Te T ν D' (b.part z)) 0)=1 from _root_.mul_eq_one_comm.mpr (crown_slot hT),one_mulVec]
end YM.RG08.Taste
