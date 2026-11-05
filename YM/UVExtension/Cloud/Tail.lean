import YM.UVExtension.Flake.Furr
import YM.UVExtension.Rafter.Late
import YM.UVExtension.Rafter.Laces
/-!
 # REAL spigot on the short-upper interval. No full-sequence assumptions.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Cloud
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard
open Fitted
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {hG:G.Simple} {M:Metals G} {P:Rolls M.p} {A:Alloy M P} {X:Roost.Factor A} (S: Uses X hG) {C:ℕ→ℝ} {W:Bid.Worth}(R:Legato.Bandage X C W)
    (d N m n:ℕ)(b:Shade)
set_option quotPrecheck false
local notation "H"=> S.fits N n
local notation "V"=> S.cart N n
local notation "τ"=> S.grove.coins
local notation "F"=> (frames G).level d
local notation "π"=> localSection G d
local notation "O!"=> hol G
local notation "J₀"=> A.B.a.clock.J m
local notation "J"=> A.B.a.clock.J (m+1)
local notation "Δ"=> P.L J
set_option quotPrecheck false
variable (hm:m<N)(hd:d+3≤A.B.a.clock.J m)
local notation "Hut"=> (S.fits N n).Hut
open UVExtension.Flake Dales Guild Lamppost Rafter Tabernacle Camp Oriel Oriel.Charted
include hm
local notation "q"=> cumulus S N m n b
local notation "Q"=> A.B.a.budget m
local notation "F0"=> A.B.a.clock.forcedAllowance m
set_option maxHeartbeats 750000 in
lemma bellows : Stalk (ChimeK G (Q) (A.B.a.S.side m n)) spreadK (fun b i x=> ↑((cumulus S N m n b m).activities.K i x)) F0:=by
   let p:=Q; let d := H|>.W m; let K:=ChimeK G p (A.B.a.S.side m n); let k:=F0; let e:= A.B.a.clock.allowance m; let Y b:=H|>.rider V τ m b m hm.le; let f z:= H|>.wave V τ m z m hm.le; let g z:= (k:ℂ) • ((f z).2.val.2); have hv: Bumps spreadK.span f∧∀ z∈ spreadK.span, f z ∈ Grip:= H|>.waved V τ m m hm.le
   let F':Readings G p (A.B.a.S.side m n)→L[ℂ] Chime K:= ContinuousLinearMap.snd ℂ ..; let P':=(Tabernacle.Box (d.hue p e k)).subtypeL; let S':=(k:ℂ) • (F'.comp P')
   have hg:Bumps spreadK.span g:= fun s i hs he hk=> S'.differentiable.comp_differentiableOn ((hv.1 s i hs he hk).snd)
   have ht : 0<k:= (fundedP m A.B.a).2
   let r(d:Shade): K.Slot := (cumulus S N m n d m).activities.K
   have hh b:g (spreadK.call b)=vibe K (r b):=by
       have hx:f (spreadK.call b)=river A.B.a m n _ (Y b.val):= H|>.spends V (S.token N n) τ m m b hm.le -- b after m? check
       unfold g; rw [hx]; change (k:ℂ) • (k⁻¹ • tuningK p _) = (vibe K (r b)); rw [← Oriel.rsmul (Chime K),smul_smul]; rw [← Complex.ofReal_mul,mul_inv_cancel₀ ht.ne',Complex.ofReal_one,one_smul]; rfl
   have he(b):∃ v,K.MeasureP (r b) v:= ⟨k, (Above.floorK p _).2 (show Activities.KBound (cumulus S N m n b m).activities p k from (fairer S N m n b hm).good.labels.boundK)⟩
   have hs z(hz:z∈ spreadK.span) : ‖g z‖≤k/2:= by
       have hv' : ‖f z‖ < rim:= mem_ball_zero_iff.mp (hv.2 z hz); have he : ‖(f z).2.val.2‖≤‖f z‖:=(le_max_right ‖(f z).2.val.1‖ ‖(f z).2.val.2‖).trans (le_max_right ‖(f z).1‖ ‖(f z).2‖)
       rw [show ‖g z‖=k*‖(f z).2.val.2‖ from (by unfold g; rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg ht.le])]
       exact (mul_le_mul_of_nonneg_left ((he.trans hv'.le).trans (by norm_num [rim] : rim≤ 1/2)) ht.le).trans_eq (by ring)
   obtain ⟨P⟩:= charmP K r g hg hh he hs; exact (Stalk.ascend P).eases (by change k/2+k/2 ≤ k; linarith)
open Extra.Histories
include R
set_option maxHeartbeats 750000 in
omit hm in
lemma wallet : Push.Local.hitWidth (A.B.a.budget m)*(A.B.a.clock.forcedAllowance m) ≤ 1 := by
   let v:= F0; let h0:= Q
   have hx := R.stamp _ _ (step_paid A.B.a m) 0 (Nat.zero_le _) (A.B.a.clock.hatBeta m) (A.B.valid.pays m)|>.2
   have hP: Push.Local.hitWidth h0 * Real.sqrt v ≤1:=by unfold v; rw [Blush.glyph_eq]; exact hx A.B.a m (params_eq A.B.valid m) rfl
   have ht := glyphBound A.B.a m; have hr: v = Real.sqrt v * Real.sqrt v:= (Real.mul_self_sqrt (fundedP m A.B.a|>.2.le)).symm
   exact (mul_le_mul_of_nonneg_left (hr.trans_le (mul_le_of_le_one_right (Real.sqrt_nonneg _) ht.2)) (zero_le_one.trans (Push.Local.width_one_le _))).trans hP
end YM.UVExtension.Cloud
