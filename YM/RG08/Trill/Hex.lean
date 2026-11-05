import YM.RG08.Halo.Screen
import YM.RG08.Trill.Cues
/-! # Chit tickets -> first hol tickets. Quantitative radial decomposition via actual canonical
 radial coordinates Place.throughSlot. Includes costs on **true node gauge**, grad sign. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Trill
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Skiff Trickle
open Room Gallery Camera Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Flint
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Lagoon Yurt Halo
open scoped Classical ContDiff BigOperators Topology ENNReal ComplexConjugate Matrix.Norms.Frobenius
variable {G:Gauge}{d n b p:ℕ}{σ B Q:ℝ}
local notation "E₀"=>Ed G Cover
local notation "Y"=>Snap G d
local notation "N"=>Nd G Cover
local notation "A₀"=>Loc G 1

-- negative node potential from generated theorem. tip is one unit, no orientation extras.
def unwell (w:E4→G.Color):N→ℝ:=fun i=> -w (Place.seat i.1) i.2
lemma splitNode {V:Masked G}(z:Y)(w:E4→G.Color)(h:Halo.relay G V=jump w+sampled z): Yurt.inlet V=pluck 1 z+grad (unwell w):=by
 funext i
 nth_rw 1 [← depict_back V,h,depict_add]
 unfold Yurt.inlet;rw [Pi.add_apply,Pi.add_apply];simp_rw [depict_apply,Pi.add_apply,pluck_lead] --
 unfold jump grad unwell; rw [Place.seat_add,Place.seat_step];change (w (Place.seat i.1) i.2.2 - w _ i.2.2) + _=_+ (-w _ _ - -w _ _);ring

private lemma unwellPoly (w:E4→G.Color)(h:w∈Place.rangeLt G.Color p): ∃ C:ℝ,Bearing (stance G.ColorIndex) p 0 C (unwell w):=by
 obtain ⟨v,_,rfl'⟩:=Halo.reading w h
 let S:=∑ i:Fin p,‖v i‖;have hS:0 ≤ S:= sum_nonneg fun i _=>norm_nonneg _
 let Q:=‖((heavy G).symm : G.Color→L[ℝ] G.ColorIndex→ℝ)‖;have hq:0 ≤ Q:= norm_nonneg _
 refine ⟨Q*S,mul_nonneg hq hS,fun i=>?_⟩
 let x:=Place.seat i.1;let a:=length i.1;have ha:0≤a:=abroad_nn i
 have hx:‖x‖≤a:=Carrier.shade_seat _
 have hv:‖w x‖≤S*(1+a)^p:=by
    rw [←rfl'];unfold Halo.mix S;rw [Finset.sum_apply,sum_mul];apply (norm_sum_le ..).trans (sum_le_sum fun j _=>?_)
    apply ((v j).le_opNorm (fun _=>x)).trans;apply mul_le_mul_of_nonneg_left _ (norm_nonneg _);rw [prod_const,card_univ,Fintype.card_fin];exact (pow_le_pow_left₀ (norm_nonneg _) (hx.trans (le_add_of_nonneg_left zero_le_one)) _).trans (pow_le_pow_right₀ (le_add_of_nonneg_right ha) j.isLt.le)
 unfold unwell hustle;rw [abs_neg,←Real.norm_eq_abs,zero_mul,Real.exp_zero,mul_one,mul_assoc];refine (norm_le_pi_norm ((heavy G).symm (w x)) i.2).trans ?_; exact ((heavy G).symm.toContinuousLinearMap.le_opNorm _).trans (mul_le_mul_of_nonneg_left hv hq)

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
lemma counterpart (G:Gauge)(d p:ℕ)(hp:p≤d):∃ C:ℝ,0≤C ∧ ∀{V:Masked G}{B:ℝ},Chit G p V B→∃ (z:Snap G d)(x:Nd G Cover→ℝ), throughSlot z p ∧ ‖z‖≤ C*B ∧ Bearing (stance G.ColorIndex) (p+1) 0 (C*B) x ∧ Bearing (stance (Loc G 1)) d 0 (C*B) (pluck 1 z) ∧ Yurt.inlet V=pluck 1 z+grad x:=by
 let E:=Loc G 1→ℝ
 let S:= Halo.Dust E p
 let X:=Module.finBasis ℝ S
 let I:= Fin (Module.finrank ℝ S)
 let f(i:I):=Halo.mix (X i)
 choose w z H using fun i:I=> Place.generated (Halo.relay G (f i)) (Place.linear_band (Halo.bonnet G).toContinuousLinearMap p (Halo.mixing _)) hp
 choose a hA using fun i:I=>unwellPoly (w i) (H i).1
 obtain ⟨U,hU,hG⟩:=Halo.industry E p
 let g(i:I):S→L[ℝ]ℝ:=LinearMap.toContinuousLinearMap (X.coord i)
 let Vz:=∑ i:I,‖g i‖*U*‖z i‖;let Vx:=∑ i:I,‖g i‖*U*a i
 have ha(i):0≤a i:=(hA i).1;have hu:0 ≤ U:=by linarith
 have hv:0 ≤ Vz:=sum_nonneg fun i (_:i∈univ)=>by positivity
 have hx:0 ≤ Vx:=sum_nonneg fun i (_:i∈univ)=>by have h:=ha i;positivity
 obtain ⟨D,hD,H₁⟩:=key_budget G d 1
 let C:= Vx+Vz+D*Vz;have hC:0≤C:=by unfold C;positivity
 refine ⟨C,hC,fun {V} {B} hb=>?_⟩; have hB:=hb.live
 obtain ⟨q,hq,hr⟩:= Halo.reading V hb.fit
 let F:S:=q
 have hf(i:I): |g i F| ≤ ‖g i‖*U*B:=by
    rw [←Real.norm_eq_abs,mul_assoc];apply ((g i).le_opNorm F).trans (mul_le_mul_of_nonneg_left _ (norm_nonneg _))
    change ‖q‖≤U*B;exact hG q hq B hB (hr.symm ▸ hb.pay)
 let Z:=∑ i:I,g i F • z i;let W:=∑ i:I,g i F • unwell (w i)
 have hZ:‖Z‖≤Vz*B:=by
    apply (norm_sum_le ..).trans;unfold Vz;rw [sum_mul];apply sum_le_sum;intro i _;rw [norm_smul,Real.norm_eq_abs];exact (mul_le_mul_of_nonneg_right (hf i) (norm_nonneg _)).trans_eq (by ring_nf;rfl)
 have hW: Bearing (stance G.ColorIndex) (p+1) 0 (Vx*B) W:=by
    apply (Bearing.sum univ (fun i (_:i∈(univ:Finset I))=>(hA i).smul (g i F))).up
    unfold Vx;rw [sum_mul];apply sum_le_sum;intro i _; exact (mul_le_mul_of_nonneg_right (hf i) (ha i)).trans_eq (by ring)
 refine ⟨Z,W, fun j hj=>?_, hZ.trans (mul_le_mul_of_nonneg_right (show Vz≤C by unfold C; nlinarith only [hv,hD,hx]) hB),hW.up (mul_le_mul_of_nonneg_right (show Vx≤C by unfold C; nlinarith only [hv,hD,hx]) hB),?_,?_⟩
 · unfold Z;rw [Finset.sum_apply];apply sum_eq_zero;intro i _;rw [Pi.smul_apply,(H i).2.1 _ hj,smul_zero]
 · have hh₁:(D*‖Z‖)=D*∏ _j:Fin 1,‖(Z:Snap G d)‖:=by simp
   have hv': Bearing (stance (Loc G 1)) (d*1) 0 (D*‖Z‖) (pluck 1 Z):=by rw [hh₁];exact H₁ (fun _=>Z)
   rw [mul_one] at hv';exact hv'.up ((mul_le_mul_of_nonneg_left hZ hD).trans (by unfold C;nlinarith)) -- nlinarith
 have he:V=∑ i:I,g i F • f i:=by
    rw [←hr];funext y
    change (Halo.preview y) F=(∑ i:I,g i F • f i) y
    conv_lhs => rw [← X.sum_repr F]
    rw [map_sum,Finset.sum_apply];simp_rw [_root_.map_smul,Pi.smul_apply];rfl
 have hi(j):Yurt.inlet (f j)=pluck 1 (z j)+grad (unwell (w j)):=splitNode _ _ (H j).2.2
 unfold Z;rw [he]; rw [pluck_combine] -- need p'=finrank
 funext j; unfold Yurt.inlet W grad;rw [Pi.add_apply,Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,←sum_sub_distrib,←sum_add_distrib];apply sum_congr rfl; intro i _
 have hh:=congrFun (hi i) j;rw [Pi.add_apply] at hh; change f i _ _ = _ + (unwell _ _ - unwell _ _) at hh
 simp_rw [Pi.smul_apply,smul_eq_mul];change g i F*f i _ _=_;rw [hh];ring
end YM.RG08.Trill
