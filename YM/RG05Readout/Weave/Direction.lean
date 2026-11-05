import YM.RG05Readout.Weave.Average
/-!
# Quantitative inverse in filled Palette, origin before test placement

Subexponential bound with exact normalized inverse products. Also store δ
suppressed Stern.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Trace.Physical Offsets OPE Copper
open Push Local MergeProof
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{b N p d m j:ℕ}{T:Emblems C d} {V:Sight C d p}{h:C.Makes}{D:Rail C}{B:ℕ→ℕ→ℝ}
-- chain r i is forward down; Order.pay at fixed k.
def finer {C:Family G}{d:ℕ} (T : Emblems C d) {m j:ℕ}(he:m ≤ j): Palette C d ≃ₗ[ℂ] Palette C d:=
    Nat.leRec (motive:=fun _i _ =>Palette C d≃ₗ[ℂ]Palette C d) (LinearEquiv.refl _ _) (fun {i} _ t=> t.trans (T i).symm) he -- check
lemma base_value : finer T (le_refl m)= LinearEquiv.refl ℂ _:=by rw [finer,Nat.leRec_self]
lemma finer_next (he:m ≤ j): finer T (show m ≤ j+1 from he.trans j.le_succ)= (finer T he).trans (T j).symm:=by rw [finer,Nat.leRec_succ (h1:=he)]; rfl -- arg

local notation "S"=> C.S
local notation "w"=> C.path.levels
noncomputable def stringCost (C:Family G) {m j:ℕ}(he:m ≤ j):ℝ:=
    Nat.leRec (motive:=fun _ _=>ℝ) 1 (fun {i} _ t=> ld C.path.levels i*t) he
lemma string_base:stringCost C (le_refl m)=1:=by unfold stringCost; rw [Nat.leRec_self]
lemma string_next (he:m ≤ j):stringCost C (he.trans j.le_succ) = ld w j*stringCost C he:=by unfold stringCost; rw [Nat.leRec_succ]
lemma lamp_nn (k:ℕ): 1 ≤ ld C.path.levels k:= Real.one_le_rpow (by exact_mod_cast (C.S.block k).property) (by positivity : 0 ≤ (1:ℝ)/((C.path.levels.clock.J (k+1):ℝ)+1))

lemma string_paid {ε:ℝ} (he:0<ε): ∀ᶠ m:ℕ in atTop, ∀ j:ℕ,∀ h:m ≤ j,stringCost C h ≤ Real.exp (ε*(C.S.scale j-C.S.scale m)):=by
    have ha: Tendsto (fun i : ℕ=> (↑(((w).clock.J (i+1))):ℝ)) atTop atTop:= (tendsto_natCast_atTop_atTop.comp ((w).fits.deep.comp (tendsto_add_atTop_nat 1))); have hb : Tendsto (fun i:ℕ=> ((((w).clock.J (i+1)):ℝ)+1)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ ha)
    obtain ⟨x,hx⟩:= eventually_atTop.mp (hb.eventually (ge_mem_nhds he))
    filter_upwards [eventually_ge_atTop x] with m hm j h
    induction j,h using Nat.le_induction with
    | base=> simp only [string_base,sub_self,mul_zero,Real.exp_zero,le_rfl]
    | succ n hn ih=>
       have he: 0<((C.S.block n).val:ℝ):=by positivity
       have hp: ld w n ≤ Real.exp (ε*((S).scale (n+1)-(S).scale n)):=by
          rw [Schedule.scale_succ,add_sub_cancel_left, mul_comm ε, ← Real.rpow_def_of_pos he]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (C.S.block n).property) (by simpa only [one_div] using hx _ (hm.trans hn))
       rw [string_next hn]; apply ((mul_le_mul_of_nonneg_left ih (zero_le_one.trans (lamp_nn (C:=C) n))).trans (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le)).trans_eq
       rw [← Real.exp_add]; congr 1; ring

lemma Spine.inverse_cost (hx:Spine D B h b p d N V T) (hb:b ≤ m) (hm:m ≤ j) (hN:j≤ N) (v:Palette C d): size (finer T hm v)≤ stringCost C hm*size v:=by
    induction j,hm using Nat.le_induction with
    | base=> simp only [base_value,string_base,LinearEquiv.refl_apply,one_mul,le_rfl]
    | succ j hm ih=>
       let v':= finer T hm v
       have hz:= (hx.follows j (hb.trans hm) hN).strength ((T j).symm v'); rw [(T j).apply_symm_apply] at hz
       rw [finer_next hm,string_next hm,mul_assoc]; exact (le_trans (size_refund ..) hz.1).trans (mul_le_mul_of_nonneg_left (ih (Nat.le_of_succ_le hN)) (zero_le_one.trans (lamp_nn _)))
end YM.RG05Readout.Address
