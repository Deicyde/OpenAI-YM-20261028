import YM.RemainderComparison.Portal.Quota
import YM.Push.STATIONARY_UNIFORM.Entries
/-!
 # RG01: Analytic profiles from authenticated path supplies

 Inputs.Admitted from the unmasked RG02 and RG03 densities. Geometry:
 all periods, cover and signed paths in actual lengths, all rank (finite load).
 No complex continuation through masks. Need widths, can share
 via epoch pricings. Estimates use fixed scalar test weights (/ positive m_i
 after root envelopes) WITHOUT dimensional losses. Stage audits later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Herbal
open Function Filter Metric Set Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext.Repeat Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.Scheduling ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Sienna Fare Germ Token
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {r j n k : ℕ}
variable {c f : Side} {S : StepData c f}
variable {E Y : Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {Z σ C D:ℝ} {s:Set E}{ι : Type}
lemma dons [CompleteSpace Y]{u:ι→E→Y}{d:ι→ℝ}(ho:IsOpen s)(hc:IsPreconnected s)(hp:SumBudget d C)(hu : ∀ i y, y∈s → Allows k (u i) y (d i)) (x:E)(hx:x∈s):
     Brush k C 1 (fun y=>∑' i,u i y) x:= by
   let L (j:ℕ) (x:E):= ∑' i, iteratedFDeriv ℝ j (u i) x; let f' (x:E):= ∑' i,u i x
   have ht (m) (hm : m≤k): Set.EqOn (iteratedFDerivWithin ℝ m f' s) (L m) s:=by
      intro y hy
      rw [iteratedFDerivWithin_of_isOpen m ho hy]
      exact iterated_at_sum ho hc hp.2.1 hu hy m hm
   have he (m) (hm:m≤k)(y)(hy:y∈s): Summable fun i=> ‖iteratedFDeriv ℝ m (u i) y‖:=
     hp.2.1.of_nonneg_of_le (fun _=>norm_nonneg _) fun i=> (hu i y hy).norm_le m hm
   have hy : ContDiffOn ℝ (↑k) f' s:= (contDiffOn_nat_iff_continuousOn_differentiableOn ho.uniqueDiffOn).mpr ⟨fun m hm=> by
      apply ContinuousOn.congr (f:=L m) _ (ht m hm)
      exact continuousOn_tsum (fun i y hy=> ((hu i y hy).analytic.continuousAt_iteratedFDeriv le_top).continuousWithinAt) hp.2.1 fun i y hy=> (hu i y hy).norm_le m hm,
       fun m hm=>by
        apply DifferentiableOn.congr (f:=L m) _ (ht m hm.le)
        intro x hx; refine (hasFDerivAt_tsum_of_isPreconnected hp.2.1 ho hc (f:=fun i=>iteratedFDeriv ℝ m (u i))
          (fun i x hx=> ((hu i x hx).analytic.differentiableAt_iteratedFDeriv (m:=m) (by simp)).hasFDerivAt) (fun i y hy=>?_) hx (he _ hm.le x hx).of_norm hx).differentiableAt.differentiableWithinAt
        rw [fderiv_iteratedFDeriv]; simpa only [Function.comp_apply,LinearIsometryEquiv.norm_map] using (hu i y hy).norm_le _ hm⟩
   refine Brush.offer.mpr ⟨hy.contDiffAt (ho.mem_nhds hx),fun m hm=>?_⟩
   change ‖iteratedFDeriv ℝ m f' x‖≤_
   rw [← iteratedFDerivWithin_of_isOpen m ho hx,ht m hm hx]
   exact (norm_tsum_le_tsum_norm (he m hm x hx)).trans ((he m hm x hx|>.tsum_le_tsum (fun i=> (hu i x hx).norm_le _ hm) hp.2.1).trans hp.2.2)
variable {U:E→ Config G f} (hu: Inputs U k Z) (H:Atom G j)(x:Site f)(p: Signed)
local notation "𝒜" => (fun z=>pull p 0 (U z))
def prize (n k :ℕ)(G:Gauge)(σ Z:ℝ) := |Work.F02.slotConst G|^k * composeCost n ((1+ (2:ℝ)^n/Work.F02.radius σ)^n) Z
lemma prizes_pos (hn:0≤Z) (hs:0<σ): 0≤prize k j G σ Z:= by have h:= Work.F02.radius_pos hs; unfold prize composeCost; positivity
include hu
lemma pulled : Inputs (𝒜) k Z:=by
   refine ⟨?_,hu.2.1,?_⟩
   · change pull p 0 (U 0)=1; rw [hu.1]; funext _; simp [pull,Lattice.Step.read]
   intro i z hz
   let d:= (posDir i.2).rotate p; let m := affine p 0 i.1; have h:=hu.2.2 (d.used m) z hz
   dsimp only []; unfold pull Lattice.Step.read; split
   · exact h.inverse (f:=fun z=> _)
   exact h
lemma currency (hσ:0 < σ)(y:E)(hy:‖y‖≤1): Allows k (fun z=> H.unmasked (pull p 0 (U z)) x) y (H.budget σ * prize k j G σ Z):=by
   let V z:= Work.F02.physical (𝒜 z); have he:Allows k V y Z:= allows_ambient (U:=𝒜) fun i=> (pulled hu p).2.2 i y hy
   have h:=mul_nonneg (show 0≤H.magnitude from by unfold Atom.magnitude; positivity) (Real.exp_pos (σ*(H.length:ℝ))).le
   have ht:=allows_real_of_entire k (Work.F02.atomExt_contDiff H x) (x:=V y) (Work.F02.radius_pos hσ) (fun z hz=>
      (Work.F02.atomExt_bound H _ hσ z (ball_subset_closedBall hz) x).trans (show _ ≤ H.budget σ * |Work.F02.slotConst G|^j from
       mul_le_mul_of_nonneg_left (by rw [← abs_pow]; exact le_abs_self _) h))
   have hP:= (ht.comp he).linear Complex.reCLM (le_of_eq Complex.reCLM_norm)
   have hv (z): Complex.reCLM (Work.F02.atomExt H x (V z))= H.unmasked (pull p 0 (U z)) x:= by
     unfold V; rw [Work.F02.atomExt_physical]; rfl
   simp_rw [hv,one_mul] at hP; apply hP.mono; apply le_of_eq; unfold prize composeCost; ring

namespace Beds
lemma allows_slot (i:Slot) : ContDiffAt ℝ ω (fun z=> i.atSite (𝒜 z) x) 0:=by
   let V z:= Work.F02.physical (𝒜 z); have he:Allows k V 0 Z:= allows_ambient (U:=𝒜) fun i=> (pulled hu p).2.2 i 0 (by simp)
   have ha z: Work.F02.colorReal G (Work.F02.slotExt i x (V z))= i.atSite (pull p 0 (U z)) x:=by unfold V; rw [Work.F02.slotExt_physical,Work.F02.colorReal_up]
   simp_rw [← ha]; exact (Work.F02.colorReal G).contDiff.contDiffAt.comp 0 (((Work.F02.slotExt_contDiff i (G:=G) x).restrict_scalars ℝ).contDiffAt.comp 0 he.analytic)
omit hu
lemma leftB {a:ι→E→ℝ}{K} (S:Finset ι)(h:∀ i∈S,Bud k K (a i) (0:E)):
    Bud k K (fun z=>∑ i∈S,a i z) 0:= by
   refine ⟨ContDiffAt.sum (fun i hi=> (h i hi).1),fun l hl hk=>?_⟩
   unfold normJ; rw [iteratedFDeriv_fun_sum_apply (f:=a) (fun i hi=> (h i hi).1.of_le (by exact_mod_cast hl)),Finset.sum_eq_zero,norm_zero]; exact fun i hi=> norm_eq_zero.mp ((h i hi).2 l hl hk)
lemma pressB {a:ι→E→ℝ}(S:Finset ι)(h:∀ i∈S,Bud k 1 (a i) (0:E)): Bud k S.card (fun z=>∏ i∈S,a i z) 0:=by
  induction S using Finset.induction_on with
  | empty=> simp only [Finset.card_empty,Finset.prod_empty]; exact ⟨contDiffAt_const,fun i _ hi=>by omega⟩
  | insert i s hi hp=>
     simp_rw [Finset.card_insert_of_notMem hi,Finset.prod_insert hi,Nat.add_comm _ 1]; exact (h _ (Finset.mem_insert_self ..)).shoot (hp fun i hi=> h i (Finset.mem_insert_of_mem hi))
include hu
lemma prestige : Bud k j (fun z=> H.unmasked (pull p 0 (U z)) x) 0:=by
   unfold Atom.unmasked Atom.poly; refine Beds.leftB Finset.univ fun i _=>?_ ; rw (occs:=.pos [1]) [← Nat.zero_add j]
   refine Bud.shoot ⟨contDiffAt_const,fun l _ hl=>by omega⟩ ?_
   rw (occs:=.pos [1]) [← show (Finset.univ:Finset (Fin j)).card = j from by simp]
   refine Beds.pressB (a:=fun l z=>(H.leg l).atSite (pull p 0 (U z)) x (i l)) Finset.univ ?_
   intro l _
   let b (z:E):=(H.leg l).atSite (pull p 0 (U z)) x
   have hb:b 0=0:=by
     unfold b; rw [show pull p 0 (U 0)=1 from (pulled hu p).1,Work.F03.atSite_path, show faceValue (1:Config G f) _=1 from (by simp [faceValue,square,travel]),G.curvature_unit,map_zero]
   have hh: (fun z:E=>WithLp.ofLp (b z) (i l))=fun z=>inner ℝ (EuclideanSpace.basisFun G.ColorIndex ℝ (i l)) (b z):=funext fun z=> (EuclideanSpace.basisFun_inner ..).symm
   refine ⟨?_,fun j hj hk=>?_⟩
   · change ContDiffAt ℝ _ (fun z:E=>WithLp.ofLp (b z) (i l)) _; rw [hh]; exact ((contDiffAt_const (c:=EuclideanSpace.basisFun G.ColorIndex ℝ (i l))).inner ℝ (show ContDiffAt ℝ ω b 0 from Beds.allows_slot hu x p _)|>.of_le le_top)
   have hj':j=0:= by omega
   subst j; unfold normJ; rw [norm_iteratedFDeriv_zero]; change ‖b 0 (i l)‖=0; rw [hb]; exact norm_zero
end Beds
end YM.RemainderComparison.Herbal
