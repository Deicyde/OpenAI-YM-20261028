import YM.RG08.Trill.Cast
import YM.Planned.PRIMARY_INTEGRAL_295.Twists
import YM.Planned.PRIMARY_INTEGRAL_295.Bigrade
/-! # Probe the literal actual lane. Common offshell coordinate extraction.
All ranks but with factor-grade cutoff; accepts any origin derivatives-real tests. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Trill
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Skiff Trickle
open Room Gallery Camera MvPolynomial Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Flint
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts
open scoped Classical ContDiff BigOperators Topology ENNReal Matrix.Norms.Frobenius
variable {G:Gauge}{d n:ℕ}
local notation "E"=>Ed G Cover
local notation "Y"=>Snap G d

def chord (i:E):Snap G d→G.Color:=lane (Place.seat i.1) (Quarry.back i.2.1)
def hi (j: G.ColorIndex) : G.Color→L[ℝ]ℝ:=(ContinuousLinearMap.proj j).comp (heavy G).symm.toContinuousLinearMap
/-- Taylor x relative root, n power of radial x *including rescaling*, true coefficient, not derivative. k-colored leg. -/
def keytar (i:E)(n:ℕ):Tensor.T Y ℝ n := (hi i.2.2).compContinuousMultilinearMap (Tensor.coeff (chord i) n 0)
def pluck (n:ℕ)(z:Y) :E→ℝ:=fun i=>Tensor.diagonal (keytar i n) z
lemma key_read (i:E)(z:Y) : chord i z=lane (Place.seat i.1) (Quarry.back i.2.1) z:=rfl
lemma hi_read (i:G.ColorIndex)(z:G.Color):hi i z=z i:=rfl
set_option maxHeartbeats 600000 in
set_option synthInstance.maxHeartbeats 400000 in
lemma key_cast (H:Hol G)(u:G.El)(i:E)(n:ℕ)(v:Fin n→Y):
 keytar i n (Drops.Cast u ∘ v)=settle u (fun j:E=>keytar j n v) i:=by
 -- defeq colorIn = Cast
 let e:Edge Cover:=(i.1,Quarry.back i.2.1)
 let L:= colorIn G d u; let P:= (G.adjoint u).toContinuousLinearMap
 have hh := (show (chord i ∘ L) =ᶠ[𝓝 (0:Y)] P ∘ chord i from light H u e)|>.iteratedFDeriv ℝ n |>.eq_of_nhds
 have he := lane_smooth (G:=G) (d:=d) (Place.seat i.1) (Quarry.back i.2.1)
 change ContDiffAt ℝ ω (@chord G d i) 0 at he
 have hJ:=Next.Foundations.jets_linear L (f:=chord i) (he.of_le (show (n:WithTop ℕ∞)≤ω from le_top))
 have hP:= P.iteratedFDeriv_comp_left he (i:=n) (show (n:WithTop ℕ∞)≤ω from le_top)
 have hG:=hJ.symm.trans hh|>.trans hP
 let q:=iteratedFDeriv ℝ n (@chord _ d i) 0 v
 have hw:=DFunLike.congr_fun hG v
 change iteratedFDeriv ℝ n (chord i) 0 (L ∘ v)=P q at hw
 change hi i.2.2 ((n.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ n (chord i) 0 (L ∘ v))=settle u _ _
 rw [hw,← P.map_smul]
 change _=P ((heavy G) (fun j=>keytar (i.1,i.2.1,j) n v)) i.2.2
 change _=P ((heavy G) (fun j=>hi j ((n.factorial:ℝ)⁻¹ • q))) i.2.2
 rfl
lemma pluck_cast (H:Hol G)(u:G.El)(z:Y):pluck n (Drops.Cast u z)=settle u (pluck n z):=funext fun i=>key_cast H u i n (fun _=>z)
lemma pluck_zero (z:Y):pluck 0 z=0:=by funext i; unfold pluck Tensor.diagonal keytar Tensor.coeff; simp [chord,lane_root]
lemma pluck_lead (z:Y)(i:E):pluck 1 z i=sampled z (Place.seat i.1) (Quarry.back i.2.1) i.2.2:=by
 change hi _ ((Nat.factorial 1:ℝ)⁻¹ • iteratedFDeriv ℝ 1 (chord i) 0 (fun _=>z))=_
 unfold chord; rw [lane_mail,iteratedFDeriv_one_apply,echoing]; change hi _ ((Nat.factorial 1:ℝ)⁻¹ • (steady (road _ _ z)+0))=_; simp only [Nat.factorial_one, Nat.cast_one,inv_one,one_smul,add_zero];rfl
lemma pluck_scale (z:Y)(s:ℝ): pluck n (s • z)=s^n • pluck n z:=funext fun i=>Tensor.homogeneous (keytar i n) z s

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
lemma key_budget (G:Gauge)(d n:ℕ):∃ C:ℝ,0≤C∧∀ (v:Fin n→Snap G d),Bearing (stance (Loc G 1)) (d*n) 0 (C*∏ i,‖v i‖) (fun i:Ed G Cover=>keytar i n v):=by
 obtain ⟨D,hD,H⟩:=mail_cap G d n
 let B:=‖((heavy G).symm : G.Color→L[ℝ] G.ColorIndex→ℝ)‖; have hB:0≤B:=norm_nonneg _
 let a:ℝ:=(n.factorial:ℝ)⁻¹; have ha:0≤a:=by unfold a; positivity
 refine ⟨B*a*D,by positivity, fun v=>?_⟩; let s:=∏ j:Fin n, ‖v j‖; have hs:0 ≤ s :=prod_nonneg fun _ _=>norm_nonneg _
 refine ⟨mul_nonneg (by positivity) hs,fun i=>?_⟩
 let T:= iteratedFDeriv ℝ n (@chord G d i) 0
 let y:=Carrier.liftCost (d*n) i.1
 have hp: ‖T v‖ ≤ D*y*s:= (T.le_opNorm v).trans (mul_le_mul_of_nonneg_right (H i.1 (Quarry.back i.2.1)) hs)
 have hv:‖hi i.2.2 (a • T v)‖≤B*‖a • T v‖:= (norm_le_pi_norm ((heavy G).symm (a • T v)) i.2.2).trans ((heavy G).symm.toContinuousLinearMap.le_opNorm _)
 rw [norm_smul,Real.norm_of_nonneg ha] at hv
 change |hi i.2.2 (a • T v)|≤ B*a*D*s*((1+abroad i)^(d*n)*Real.exp (0*abroad i));rw [zero_mul,Real.exp_zero,mul_one,← Real.norm_eq_abs]
 refine hv.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp ha) hB).trans_eq ?_); change _=B*a*D*s*y;ring
end YM.RG08.Trill
