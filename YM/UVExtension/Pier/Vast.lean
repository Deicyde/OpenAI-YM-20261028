import YM.UVExtension.Pier.Ale
import YM.UVExtension.Gale.Pots
/-!
  # Bottom-up continuation. For any chosen multiplied support budget, no
  volume toll or losses exponential per derivative. No denominators required
  at intermediate levels on the complex disk. This is polynomial a priori
  control of an unbounded-density family of possible anchored tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Pier
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Lotus
open Progress.DirectedRecipe Eyelet Extra.Histories MeasureTheory Push Push.AbsoluteSums
open RG.Supply Precision Shoot Org Input Steady
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext Mallow Blush
open WilsonStartup Time Next.Foundations UVNext.CouplingReset Legato
open Roost Spire Orchard Camp Dales Lamppost Oriel Rafter Copse Linden
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {hG:G.Simple}{X: Metals G} {D:Rolls X.p} {A : Alloy X D} {R:Factor A} (S: Uses R hG)
    (N n m k:ℕ) {a z:ℝ}(ha:0<a)(hp:Metric.ball (0:ℂ) a ⊆ Camp.Broad A.B.a) (hm:m<N)
set_option quotPrecheck false
local notation "T"=> desk a ha
local notation "Y"=> Row a
local notation "V"=> fun (b:Row a) m=> S.realBeat b.val N n m
local notation "X1"=> mount R N (m+1) n 0 (A.B.a.clock.hatBeta (m+1)) 0
local notation "P₁"=> A.B.a.budget (m+1)
local notation "P"=> A.B.a.budget m
local notation "L"=> D.L (A.B.a.clock.J (m+1))
local notation "T₀"=> A.B.a.S
variable {x:ℕ→ℝ} (hR: Mallow.Arrives R.shape A.delay)(hr:∀ i j,(R.target i j).rate ≤ -(7/16:ℝ))(hw: UVExtension.Cloud.Leases x R.shape A.delay) -- UV name
include hm hp hw hr hR
local notation "v"=> R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)
local notation "n₁"=> A.B.a.S.side (m+1) n
local notation "s"=> fun i=> z*((T₀).a i)⁻¹^3
lemma promoted (hx:0 ≤ z) (hk:k ≤ A.B.a.clock.J m) (hf:Harbour T k (P) (fun b:Y=> S.realBeat b.val N n m) (s m)): Harbour T k P₁ (fun b:Row a=> S.realBeat b.val N n (m+1)) (s (m+1)):= by
    let q:= T₀; intro i h x'
    let f:= x'.val; let b':=s m; have hu:0 ≤ b':= mul_nonneg hx (pow_nonneg (inv_nonneg.mpr (q.a_pos _).le) _); let ξ:=‖Pin P₁ i x'‖; let p:= land G n₁ P₁ i
    by_cases hz:f=0
    · have h₁(b:Y): Pier.hit (V b (m+1)) i f=0:=by rw [hit,hz,mul_zero]; simp [total]
      have h₂:(fun b:Y=> Pier.hit (V b (m+1)) i f)=fun _=>0:=funext h₁
      change Sail _ (fun b=> Pier.hit (V b (m+1)) i f) _; rw [h₂]; exact ⟨_, bumps _ (fun _=>0) (differentiableOn_const _),fun _=>rfl,fun _ _=> by rw [norm_zero]; exact mul_nonneg (mul_nonneg (mul_nonneg hx (pow_nonneg (inv_nonneg.mpr (q.a_pos _).le) _)) (Real.exp_pos _).le) (norm_nonneg _)⟩
    have h₀: (0:Site n₁)∈ p:= (held _ _ x').here hz; let ψ:= q.block m; have hX:3≤ (ψ.val:ℝ):= by exact_mod_cast q.block_large m
    have he0: HasSlots P₁ (X1).activities:= ⟨rfl,rfl,fun _=>rfl,fun _=>rfl⟩
    let θ:= X1; let c(b:Y)(q':ℂ→L[ℝ]ℝ)(hρ:∀ u,‖q' u‖≤‖u‖): Leaf (V b (m+1)):= moor P₁ i x' h q' hρ (V b (m+1)) rfl (poss S N n (m+1) (roseK S ha hp b) hm)
    let t:= Copse.worth k (P₁).B (P₁).supportExponent p; have ht₁:0≤t:=(Real.exp_pos _).le; let η:=b'*((ψ.val:ℝ)*t*ξ); have ht(q':ℂ→L[ℝ]ℝ)(hρ:∀ u,‖q' u‖≤‖u‖): Pier.Sail T (fun b:Y=> total (V b (m+1)) (Complex.ofReal ∘ (c b q' hρ).cicada)) (η+η):=by
       let M:= moor (Q:=θ) P₁ i x' h q' hρ rfl he0; let Q:= fun b:Y=>c b q' hρ; let T':=(A.B.a.clock.op m n).ratio
       have hx : M.crest=p:= whereAt i rfl he0; have hy:T'.parent 0=0:=(show T'.embed 0=0 from T'.root.map_zero) ▸ T'.embed_parent 0
       have hM: Guarded R M:=⟨h⟩; let u:=2*budgetsP M v k
       have hF:= hauls S N n m ha hp hm M hM Q (fun _=>rfl) (fun _=>rfl) k (Finset.mem_image.mpr ⟨0,hx.symm ▸ h₀,hy⟩) (UVExtension.Cloud.wiggles R x hw hr m) hR hu hf
       have hz:u≤(ψ.val:ℝ)*t*ξ:=by
          have ht': 24*coined v k ≤ (ψ.val:ℝ):= by rw [show ψ= _ from PriceCompiler.block_eq A.B.valid m]; exact hw.hearty _ _ (step_paid A.B.a m) _ (hk.trans (A.B.a.fits.mono m.le_succ))
          unfold u budgetsP Linden.prices; rw [hx]; change 2*(12*(coined _ _*(ξ*t)))≤(ψ.val:ℝ)* t*ξ; rw [show 2*(12*(coined _ _*(ξ*t))) = 24*coined v k*(ξ*t) by ring, show (ψ.val:ℝ)*t*ξ=(ψ.val:ℝ)*(ξ*t) by ring]; exact mul_le_mul_of_nonneg_right ht' (mul_nonneg (norm_nonneg _) ht₁)
       exact hF.mono (add_le_add (mul_le_mul_of_nonneg_left hz hu) (mul_le_mul_of_nonneg_left hz hu))
    let X b:=c b Complex.reCLM Blush.juror; let W b:= c b Complex.imCLM Blush.jurorI
    have hc : (fun b:Y=> Pier.hit (V b (m+1)) i f)=(fun b:Y=> total (V b (m+1)) (Complex.ofReal ∘ (X b).cicada)+ Complex.I*total (V b (m+1)) (Complex.ofReal ∘ (W b).cicada)):= by
       funext b; exact complexify P₁ (V b (m+1)) (liveR S N n (m+1) (roseK S ha hp b) hm) i x' (X b) (W b) rfl rfl (fun U=>Eq.trans ((Complex.re_add_im (f U)).symm) (congr_arg (fun z=>( (f U).re:ℂ)+z) (mul_comm ..))) -- ambiguous
    have ht' : (s (m+1))=b' * (ψ.val:ℝ)^3:=by simp only; rw [q.a_step m]; change z*_ = (z* _)*_; simp [div_eq_mul_inv,mul_pow,mul_assoc,mul_comm,q,ψ]
    have hL: (4:ℝ)* (ψ.val:ℝ)≤ (ψ.val:ℝ)^3:=by nth_rw 1 [pow_succ]; exact mul_le_mul_of_nonneg_right (by nlinarith only [hX]) (by positivity)
    change Pier.Sail (desk a ha) (fun b:Y=> Pier.hit (V b (m+1)) i f) ((s (m+1))*t*ξ); rw [hc,ht']; refine ((ht _ Blush.juror).plus ((ht _ Blush.jurorI).scales Complex.I)).mono ?_
    rw [Complex.norm_I,one_mul]; unfold η; calc
     _= b'*(4*ψ.val)*t*ξ:=by ring
     _≤_:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL hu) ht₁) (norm_nonneg _)
omit hm
lemma earnsV (hx:0 ≤ z) (r:ℕ)(hk:k ≤ A.B.a.clock.J r) (hf: Harbour (desk a ha) k (A.B.a.budget r) (fun b:Row a=> S.realBeat b.val N n r) (s r))(hc:r ≤ m)(hm:m≤N): Harbour (desk a ha) k (A.B.a.budget m) (fun b:Row a=> S.realBeat b.val N n m) (s m):= by
    induction m,hc using Nat.le_induction with
    | base=> exact hf
    | succ m hc ih=> exact promoted S N n m k ha hp hm hR hr hw hx (hk.trans (A.B.a.fits.mono hc)) (ih (m.le_succ.trans hm))
end YM.UVExtension.Pier
