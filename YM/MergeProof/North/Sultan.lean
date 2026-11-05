import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Estimate
import YM.MergeProof.North.Brick

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Station Next.Rank.Spindle Cells
open scoped Topology BigOperators Classical
section
open Relay Exponential Extraction Bid PhysicalNext.Repeat.Legato.Bandage
variable {G:Gauge}(C:Family G)(N p J k j m D d h:ℕ) {r:ℕ→ℕ} {W:Bid.Worth} {u ψ φ δ:ℕ→ℝ} {μ:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "H"=> C.path
local notation "P"=> C.path.levels.budget
local notation "Y"=> C.path.levels
local notation "V"=> Site (C.side J p)
local notation "rad"=> fuga C.path.levels (m+1)
variable (x:Cover)(B: C.label d) (T:C.label 4) (hf:J ≤ k) (hk:k ≤ m) (hm:m+1 < j) (hj:j<N)
local notation "f"=> Next.UVStress.fragment (C:=C) (D:=D) (d:=d) h rad T B j x N p
local notation "τ"=> center C.S p (le_trans hf (le_trans hk (le_trans (m.le_succ) (le_trans hm.le hj.le)))) 0
variable (hh:C.Makes)(hR:Created C)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r μ)
-- financial b.E
variable {i₀:ℕ}{σ χ:ℕ→ℝ}
include hh
def whims (b a:ℝ) (w:Bool) : ℝ:= if w then plumR C 4 b j/(fuga C.path.levels (m+1))^h else plumR C d a j
omit hh in
lemma fugap : 0 < rad:= mul_pos (mul_pos (by norm_num) (pow_pos (by exact_mod_cast (C.path.levels.budget (m+1)).B_pos) _)) (C.S.a_pos _)
variable (b a e X η c:ℝ)
omit hh in
lemma fundR (ha: 0 < a)(hb:0<b) (i:Bool) : 0< whims C j m d h b a i:=by
    unfold whims; split
    · exact div_pos (stockpit _ _ _ _ hb) (pow_pos (fugap ..) _)
    exact stockpit _ _ _ _ ha
local notation "A"=> whims C j m d h b a
variable (hB:(C.labels.level d).coeffSize B ≤ a) (hT:(C.labels.level 4).coeffSize T ≤ b)
local notation "ℓ"=> wrap (C.side j p) x
local notation "L"=> bites C J j p ℓ
local notation "O"=> location C.S j N p x
local notation "W'"=> ventola C.path.levels j (m+1) δ φ η A
lemma paid_new (q:C.label d)(r:ℝ)(hr:0<r)(hr':(C.labels.level d).coeffSize q ≤r)(he:C.ref d≤j)(hn:j < N): plumR C d r j * Spindle.paid C d j N p q ≤ fly (Y) d j:=by
    exact (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (paid_pos ..) (C.path.levels.params _).columns_ge) (stockpit C j _ r hr).le).trans (stocking C N j p d q r hr he hn.le hh hr')
include hp in
lemma paid_scale (hr:C.ref d ≤ j) (q:C.label d)(a:ℂ)(hn:j ≤ N):Spindle.paid C d j N p (a • q)=‖a‖* Spindle.paid C d j N p q:=by
    unfold Spindle.paid Price.awake Price.columns
    let S:=C.factory d N p; obtain ⟨M,hI,hS,hK,hY⟩:= (hp.costs.aim d N p (hr.trans hn)).lyrics
    have hX(a:ℂ) (u:C.label d): (S.entries j (a • u)).x=a •(S.entries j u).x:=by
       unfold S; rw [hI]; change ((M.tone j).plays _|>.x) = _ • ((M.tone j).plays u|>.x); rw [(hS.earned j hr hn).currents, (hS.earned j hr hn).currents,map_smul]
    simp only [map_smul]; change (C.labels.level d).coeffSize (_ •(S.entries j _).x)=_; rw [hX a,smul_comm,Size.smul]
    -- inspect. 
lemma itemT (r:C.label d) (v:Site (C.side N p)): stepUp (1,false) v (C.O N p r 0) = C.O N p r v:= by
   funext s; unfold stepUp; dsimp only; rw [pull_one]; change C.O N p r 0 (translate v s)=_; simpa using C.translation 0 v r s
end
end YM.MergeProof.Ribbons
