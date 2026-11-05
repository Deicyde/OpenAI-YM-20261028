import YM.RG08.Pill.Spoil
/-!
# Check transmissions in any normalization, using true letter slots. PC inputs
at finite-order expansions.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Pill
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Matrix Summit PertExtension.Series.Tested PertExtension.Series.Radial Scores PowerSeries Door
open scoped BigOperators Topology Real ContDiff
variable {X:Chain}{G:Gauge}{E e N r d τ D j t i k m l n s :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
open Wings Summit
local notation "⨯" => (PowerSeries.X:PowerSeries ℝ)
local notation "Z" => ladder X ν D' N
variable {I:Type}{u:I→Windows}
-- emission covariance at local step and reference. `stateU` normalized HT from master vector at reporting k.
def freight {I:Type}(p:PowerSeries ℝ)(v: Native I): Native I:= fun i=> PowerSeries.subst p (v i)
lemma torque {J:Type}[Fintype J](p:PowerSeries ℝ)(hp:HasSubst p)(A:Session J)(v:Native J): freight p (A*ᵥ v)= awake p A *ᵥ freight p v := by
  let f: PowerSeries ℝ→ₐ[ℝ] PowerSeries ℝ:=PowerSeries.substAlgHom hp; have he: (f:PowerSeries ℝ→PowerSeries ℝ)=PowerSeries.subst p:= coe_substAlgHom _
  ext1 i; unfold freight awake mulVec dotProduct; simp_rw [map_apply]; rw [← he,_root_.map_sum]; exact sum_congr rfl fun i _=> _root_.map_mul ..
lemma torpedo {J:Type}[Fintype J](p q:PowerSeries ℝ)(hp:HasSubst p)(hq:HasSubst q)(A:Session J): awake p (awake q A)=awake (PowerSeries.subst p q) A:= by
    ext1 i j; simp only [awake,map_apply,subst_comp_subst_apply hq hp]
variable (X ν D')
def forward (N i k:ℕ)(v:Native (Letter F)): Native (Letter F):= freight (ladder X ν D' N k i) v
variable {X ν D'}
lemma forward_inverse (N i k)(v:Native (Letter F)): forward X ν D' N k i (forward X ν D' N i k v)=v:= by
   funext a; unfold forward freight; rw [subst_comp_subst_apply (.of_constantCoeff_zero' (look ..)) (.of_constantCoeff_zero' (look ..)),global,notary,X_subst]
lemma cashStep (N i k)(v:Native (Letter F)): swapU (dance X ν D' N i).scale (forward X ν D' N (i+1) k v) = forward X ν D' N i k v:= by
   funext p; unfold swapU forward; rw [show ⨯*(dance X ν D' N i).scale=ladder X ν D' N (i+1) i from rfl, freight,subst_comp_subst_apply (.of_constantCoeff_zero' (look ..)) (.of_constantCoeff_zero' (look ..)),global]; rfl
lemma step_basis (ht:Tights T S ν D' u)(t:Wings u 1)(K:ℕ) (v:Native (Letter F)) :
    Needle.push (heights X ν D' t) d d (edgeBook (Ye X ν D' T t.up) (forward X ν D' t.N (t.i+1) K (awake (ladder X ν D' t.N t.i K) ((Te T ν D' t)⁻¹) *ᵥ v))) = edgeBook (Ye X ν D' T t.low) (forward X ν D' t.N t.i K v) := by
  let P := Te T ν D' t; let H:= awake (ladder X ν D' t.N t.i K) P⁻¹
  rw [study _ _ (ht.fair _) h (ht.firs _|>.toBoards),show uprise _ _= _ from (ht.reads t).2]; erw [cashStep]; rw [telephone]
  apply congr_arg (edgeBook (Ye X ν D' T t.low)); unfold forward; rw [torque _ (.of_constantCoeff_zero' (look ..)), torpedo _ _ (.of_constantCoeff_zero' (look ..)) (.of_constantCoeff_zero' (look ..)),global,notary,show awake ⨯ _ = P⁻¹ from ?_,mulVec_mulVec, Matrix.mul_nonsing_inv _ (recoupC (ht.reads _|>.1)),one_mulVec]
  · ext1 i j; exact PowerSeries.X_subst _ -- path
lemma step_bridge (ht:Tights T S ν D' u)(x: ShoreP u)(he : i < x.city)(V:Native (Letter F)): let q:= face x i he; let M:=trump T ν D' x.next.N x.low x.next.main
    Needle.push (heights X ν D' q) d d (edgeBook (Ye X ν D' T q.up) (forward X ν D' q.N (q.i+1) x.next.main ((M (i+1))*ᵥ V)))= edgeBook (Ye X ν D' T q.low) (forward X ν D' q.N q.i x.next.main ((M i)*ᵥ V)) := by
   intro q M
   let S:= awake (ladder X ν D' q.N q.i x.next.main) ((Te T ν D' q)⁻¹)
   have hV : M (i+1)= S * M i:= rfl
   rw [hV,← mulVec_mulVec]; exact step_basis ht q _ _
end YM.RG08.Pill
