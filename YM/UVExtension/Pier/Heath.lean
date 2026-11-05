import YM.UVExtension.Pier.Plates
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Pier
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Lotus
open Progress.DirectedRecipe Eyelet Extra.Histories MeasureTheory Push Push.AbsoluteSums
open RG.Supply Precision Shoot Org Input Steady
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext Mallow
open WilsonStartup Time Next.Foundations UVNext.CouplingReset Legato
open Roost Spire Orchard Camp Dales Lamppost Oriel Rafter Copse Linden Metric
open SectorNext.Vacuum Hearth
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {hG:G.Simple}{X: Metals G} {D:Rolls X.p} {A : Alloy X D} {R:Factor A} (S: Uses R hG)
    (N n m k:ℕ) {a z p:ℝ}(ha:0<a)(hp:Metric.ball (0:ℂ) a ⊆ Camp.Broad A.B.a) (hm:m≤N)
set_option quotPrecheck false
local notation "T"=> desk a ha
local notation "Y"=> Row a
local notation "V0"=> fun (N:ℕ)(b:ℝ) => S.realBeat b N n m
local notation "P"=> A.B.a.budget m
local notation "T₀"=> A.B.a.S
local notation "Z"=> ball (0:ℂ) a
local notation "n₀"=> A.B.a.S.side m n
local notation "μ"=> prior G n₀
lemma Sail.shrink {f:ℝ→ℂ}(h:Sail T (fun d:Y=> f d.val) p)(ht:0<z)(hx:z≤a): Sail (desk z ht) (fun d:Row z=> f d.val) p:=by
   obtain ⟨g,hg,hQ,h⟩:= h; exact ⟨g,fun t v hs hh he=>hg t v hs (fun x hx'=> ball_subset_ball hx (hh hx')) he, fun i=> hQ ⟨i.val,i.property.trans_le hx⟩,fun v hv=> h _ (ball_subset_ball hx hv)⟩
include hp ha
lemma mounted : ∃ s v:ℝ, ∃ hs:0 < s, s ≤ a ∧ 0≤v ∧ ∀ N,m ≤N→ Harbour (desk s hs) k P (fun d:Row s=> S.realBeat d.val N n m) (v*(A.B.a.S.a m)⁻¹^3) :=by
   obtain ⟨p,z,h₁,h₂,h⟩:=roomR S n m ha hp; obtain ⟨t,ht,hV,H⟩:=zeroFree ha h₁ h₂
   let u:=z/2; have hu:0 < u:= half_pos h₂
   let v:=u⁻¹*p; have hv:0≤v:=mul_nonneg (inv_pos.mpr hu).le h₁.le; let f(N:ℕ)(i:ℝ):= ∫ U,stripped (V0 N i) U ∂μ
   refine ⟨t,v,ht,hV.le,hv,fun N hm i he x=> ?_⟩
   let V(d:Row t):= V0 N d.val
   have hF : Sail T (fun d:Y=> (f N d.val:ℂ)) p:=by
       let w:= (Sail.integral (μ) h₁.le (fun U=> h N hm|>.1 U|>.1) (fun d=>((stripped_int _ (liveR S N n m (roseK S ha hp d) hm))).ofReal)); unfold f; simp_rw [← integral_complex_ofReal]; exact w
   have hp': Sail (desk t ht) (fun d:Row t=> ((f N d.val:ℂ))⁻¹) u⁻¹:=by
       obtain ⟨g,hg,hQ,hg'⟩:= hF
       have he : DifferentiableOn ℂ g Z:= hg _ id isOpen_ball (mapsTo_id _) differentiableOn_id
       let p0:Y:=⟨0,abs_zero.trans_lt ha⟩; have hz: z ≤ ‖g 0‖:=by rw [show g 0=(f N 0:ℂ) from hQ p0,Complex.norm_real]; exact ((h N hm).2 p0).trans (le_abs_self _)
       have hG:= H g he hg' hz; have hp : DifferentiableOn ℂ (fun d=> (g d)⁻¹) (ball 0 t):=(he.mono (ball_subset_ball hV.le)).inv fun z hz=> (norm_pos_iff.mp (hu.trans_le (hG z hz)))
       refine ⟨fun d=> (g d)⁻¹, bumps _ _ hp,fun i=> congr_arg Inv.inv (hQ ⟨i.val,i.2.trans hV⟩),fun d hd=>?_⟩; exact (norm_inv _).trans_le (inv_anti₀ hu (hG d hd))
   let ξ:= ‖Pin P i x‖
   have hp₁(U): Sail (desk t ht) (fun d:Row t=> faded (V d) i U*x.val U) (p*ξ):= ((Sail.shrink (f:=fun d=>faded (V0 N d) i U) ha ((h N hm).1 U|>.2 i) ht hV.le).scaled _).mono (mul_le_mul_of_nonneg_left ((charged _ _ x|>.mp (le_refl ξ)) U) h₁.le)
   let w(d:Row t):= ∫ U,faded (V d) i U * x.val U ∂μ
   have hD: Sail (desk t ht) w (p*ξ):=by
       refine Sail.integral μ (mul_nonneg h₁.le (norm_nonneg _)) (fun i=>hp₁ i) (fun d=>?_)
       let d':Y:=⟨d.val,d.2.trans hV⟩; exact ((strips _ (liveR S N n m (roseK S ha hp d') hm) i).mulC (show Envelope x.val from ⟨(held _ _ x).mesh,(held _ _ x).paid⟩)).integrableC _
   have hh:= hp'.mult hD (inv_pos.mpr hu).le
   let Y':= Copse.worth k (P).B (P).supportExponent (land G n₀ (P) i); have hA:1 ≤ Y':= Real.one_le_exp (mul_nonneg (P).exponent_pos.le (Nat.cast_nonneg (α:=ℝ) _)); let Q:=T₀; have he:1≤(Q.a m)⁻¹:= (one_le_inv₀ (Q.a_pos _)).2 ((Q.strictAnti.antitone (Nat.zero_le _)).trans_eq (Q.a_zero)); have ht': v ≤ v*(Q.a m)⁻¹^3:= le_mul_of_one_le_right hv (one_le_pow₀ he)
   simp_rw [hitStrip]; change Sail _ (fun d=> _* w d) _; exact hh.mono ((mul_assoc ..).symm.trans_le (mul_le_mul_of_nonneg_right (ht'.trans (le_mul_of_one_le_right (hv.trans ht') hA)) (norm_nonneg _)))

-- from all inserted receive
variable {C:ℕ→ℝ}{w:Bid.Worth}(R': Bandage R C w) (hr:∀ i j,(R.target i j).rate ≤ -(7/16:ℝ))(hw: UVExtension.Cloud.Leases C R.shape A.delay)
include hp hr hw R' ha
lemma boot : ∃ m s v,∃ hs:0 < s, s≤ a∧0≤v∧∀ n' N,m ≤ n' → n'≤N→Harbour (desk s hs) k (A.B.a.budget n') (fun d:Row s=> S.realBeat d.val N n n') (v*(A.B.a.S.a n')⁻¹^3):=by
   obtain ⟨m,hM⟩:= (A.B.a.fits.deep.eventually_ge_atTop k).exists
   obtain ⟨s,v,hs,h₁,h₂,h⟩:=mounted S n m k ha hp
   exact ⟨m,s,v,hs,h₁,h₂,fun i N hi hm=> earnsV S N n i k hs (Subset.trans (ball_subset_ball h₁) hp) R'.r hr hw h₂ m hM (h N (hi.trans hm)) hi hm⟩
end YM.UVExtension.Pier
