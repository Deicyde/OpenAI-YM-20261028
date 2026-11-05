import YM.RG08.Plot.Alto
import YM.RG08.Taste.Table
/-!
# Instantiate with primary bare stencils exactly from Élan
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Plot
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town Bands Pill Wings High PowerSeries Taste
open scoped BigOperators Topology Real ContDiff
variable {I J M:Type} {u:I→Windows}{n k i:ℕ}{X:Chain}{G:Gauge}{E e r d τ D j t l:ℕ}{ν:G.ColorIndex}{F:Labels.Frame G d}{Ω:SectionData F}{H:Hol G}{D':ChartRatio G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}{R:ℝ}{h:1/2≤R}{hD:d+1≤D}{T:Signals P Q E τ H Ω h hD}{A:Grotto G P k E τ}
variable {b:J→ Dial u}{z a:M→ℕ}{p:List M} {C B C':J→ℝ} {U V:J→Native (Letter F)}
section enroll
variable (X ν D')
def masters (T:Signals P Q E τ H Ω h hD)(N k i:ℕ)(U:Native (Letter F)) := edgeBook (stepboard X ν D' H Ω (d.le_succ.trans hD) h N i) (forward X ν D' N i k ((trump T ν D' N k k (i-k))*ᵥU))
variable {X ν D'}
local notation "Ⓨ" => High.glass X (b:=b) (n:=0)
local notation "⚡" => High.defect (n:=0) (b:=b) X
local notation "▲" => masters X ν D' T
variable (he:Tights T S ν D' u)
include he
lemma mastery (i:High b 0)(v:Native (Letter F)): Marvel d (▲ (b i.z).N (b i.z).K i.i v) ∧ Lank (▲ (b i.z).N i.K i.i v):=edge_crew _ _ (he.firs i.appr|>.toBoards) le_rfl
lemma mast_step (t:High b 1)(u':Native (Letter F)):
   let V:= ▲ (b t.z).N t.K t.i u'; let W:= ▲ (b t.z).N t.K (t.i+1) u'; V=Needle.push (heights X ν D' t.appr) d d W:= by
    intro V W; let p:= t.i-t.K
    let N:=(b t.z).N; let T':=Te T ν D' t.appr; let A n:= trump T ν D' N t.K t.K n
    let M := awake (ladder X ν D' N t.i t.K) T'⁻¹
    have hp : A (t.i+1-t.K) = M*A p:= by
       rw [show t.i+1-t.K=p+1 by have he:=t.heap; change t.i+1-(b t.z).K=t.i-(b t.z).K+1; omega]; unfold A trump; unfold firstT; rw [turn]; congr 1
       change awake (ladder X ν D' N (t.K+p) t.K) (dice X ν D' H Ω _ _ N (t.K+p))⁻¹=M; rw [show t.K+p=t.i from Nat.add_sub_of_le t.heap]; rfl
    change edgeBook (Ye X ν D' T t.appr.low) (forward X ν D' N t.i t.K ((A p) *ᵥ u'))=Needle.push _ _ _ (edgeBook (Ye X ν D' T t.appr.up) (forward X ν D' N (t.i+1) t.K ((A (t.i+1-t.K))*ᵥu')))
    rw [hp, ←mulVec_mulVec]; exact Eq.symm (step_basis he t.appr t.K _)
omit he in
lemma dialP (t: Dial u)(X:Chain): Audience (fun _ : Unit=> Dial.fee X t):= fun _=> age_one (u _|>.pos) ..
omit he in
private lemma hintT (hp: Tonic (fun i=> Dial.fee X (b i)) B (fun i=>gain X.S (1/4) (b i).K (b i).N) C C')(hx:0 ≤ B) : Tonic Ⓨ (fun i=> B i.z) ⚡ (fun j=> C j.z) (fun j=> C' j.z):= by
   let hP:= Tonic.viaD hp (High.z (n:=0) (b:=b)); let y:= (fun i:High b 0=> Dial.fee X (b i.z)); have hz {q U:High b 0→ℝ}(h:Dig y q U): Dig Ⓨ q U:= ⟨_,(here_bill X).sway (glint X b 0) h.asset.choose_spec.1,h.asset.choose_spec.2⟩
   refine ⟨hz hP.one,hz hP.two,Taste.Dig.riseD (hz hP.both) (fun i=> mul_le_mul_of_nonneg_right (show gain X.S (1/4) (b i.z).K (b i.z).N ≤ gain X.S (1/4) i.i (b i.z).N from Real.exp_monotone (by have he:= age_scale_mono X.S i.heap; linarith)) (hx i.z))⟩
lemma mastery_d (hk:e≤ E)(p:J→ℝ)(hp:0 ≤ p)(hx:∀ j≤ E,∀ a: Letter F,Tonic (fun i=> Dial.fee X (b i)) p (fun i=> gain X.S (1/4) (b i).K (b i).N) (fun j'=> coeff j (U j' a)) (fun j'=> coeff j (V j' a))) k' :
   Drum k' Ⓨ ⚡ (fun i=>p i.z) (fun i:High b 0=> ▲ (b i.z).N i.K i.i (U i.z) e r) (fun i=>▲ (b i.z).M i.K i.i (V i.z) e r) 1:= by
    let A i:= High.waitP (b:=b) i
    have hZ i hi b':= hintT (hx i hi b') hp
    have hC: Weighed Ⓨ (fun i=> (A i).y X):= by unfold A; simp_rw [High.spend]; simpa only [pow_one] using Weighed.power _ (glint X b 0) 1
    have hL i (hi:i≤ E) a:= trump_d he A hC (fun i=>le_of_eq (High.joust X i)) (ρ:=fun i=>p i.z) (fun i=> hp i.z) (glint X b 0) (A:=fun i=>U i.z) (B:=fun i=>V i.z) (fun j hj a=> hZ j (le_trans hj hi) a) hi a -- hi binder
    let Z i:=Ye X ν D' T (High.appr (b:=b) (n:=0) i)
    refine heads_up (Z:=Z) (H':=fun i=> Ye X ν D' T i.appr.wingR) (fun i=> (he.firs _).toBoards) (fun i=>(he.firs _).toBoards) (High.glint _ _ _) (fun i=>(gain_pos ..).le) (fun i hi p r=> (Lens_pay he (hi.trans hk) p r k').mold High.appr) (hm:=fun i hi a=>?_) -- refine explicit
    let S i:= A i|>.next; have hu(i): (S i).cost X= ⚡ i:= High.joust X _
    refine forward_d he (b:=fun i=> (A i).next) ?_ (fun i=>le_of_eq (hu i)) (fun i=>hp _) (High.glint _ _ _) (fun j hj b=> hL j ((hj.trans hi).trans hk) b) (hi.trans hk) a
    simpa only [pow_one] using! Weighed.power Ⓨ (High.glint _ _ _) 1 -- fix
omit he in
lemma mateR (hx: Dig (fun i=> Dial.fee X (b i)) C B): Tonic (fun i=> Dial.fee X (rightT b i)) C (fun i=>gain X.S (1/4) (rightT b i).K (rightT b i).N) B B:= ⟨hx,hx,by rw [sub_self]; exact Dig.zero⟩
end enroll
end YM.RG08.Plot
